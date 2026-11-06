-- Prove2me | Theorems.Thm_FracTruthSched_lemma_1
-- name    : FracTruthSched.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:45.077076+00:00
-- url     : https://prove2.me/theorems/924645c7-438e-4342-95d7-79d9bf1278ab
-- title:
--   Lemma 1 (Padding) — a truthful mechanism on $MC_\ell$ with load bound (7) and properties (i)–(iv)
-- statement:
--   Let $n\ge1$ and let $R=(R_m)_{m\ge1}$ be a family of deterministic truthful fractional mechanisms on $n$ machines, one for every finite number $m$ of tasks, with finite worst-case approximation ratio $\rho$ against the integral optimum:
--   $$\mathrm{Mech}_{R_m}(t)\le\rho\,\mathrm{Opt}(t)\quad\text{for every } m \text{ and every nonnegative input } t \text{ with } \mathrm{Opt}(t)>0.\tag{3}$$
--   Then for every $\ell\ge2$ there is a feasible truthful fractional mechanism $(x,P)$ on the core tasks of $MC_\ell$, defined at all nonnegative real graph inputs, such that
--   $$\mathrm{Mech}_x(t)\le\rho\,C(t)\quad\text{for every graph input } t,\tag{7}$$
--   including inputs with $C(t)=0$, and which also satisfies:
--
--   1. (i) eligibility: edges go only to their endpoints and self-loops only to their owners;
--   2. (ii) unique zeros: every edge with a unique zero-cost endpoint goes wholly to that endpoint;
--   3. (iii) zero-type irrelevance (Definition 4);
--   4. (iv) symmetry: relabelling tasks within any class $Q_{\{i,j\}}$ relabels the allocation in the same way, and leaves every machine's disutility unchanged.
--
--   Consequently, if $(x,P)$ has approximation ratio greater than $\rho'$, the original family also exceeds $\rho'$ on some finite input with positive optimum: the same mechanism satisfies (7) with $\rho'$ in place of $\rho$ for every $\rho'$ for which the family satisfies (3).
--
--   The lemma reduces the lower bound for arbitrary families to a single mechanism on a fixed finite graph with strong structural properties.
--
--   Differences from the source:
--   - generalization: ρ the finite worst-case approximation ratio of R against the integral optimum → any real ρ satisfying (3) for the family; reason: the worst-case ratio satisfies (3), so the statement specializes to the source's; it is the form the proof of Theorem 2 uses (p.18: 'the original family, whose approximation ratio is at most ρ′')
--   - encoding: Consequently, if (x, P) has approximation ratio greater than ρ′, the original family also exceeds ρ′ on some finite input with positive optimum → the same M satisfies Mech_x(t) ≤ ρ′ C(t) at every graph input for every ρ′ for which the family satisfies (3); reason: contrapositive of the sentence (App. A.4, Claim 10); the remark that Section A.4 gives a direct extraction is about the proof and is not a claim
--   - encoding: (R_m)_{m≥1}, one mechanism for every finite number of tasks → R : (m : ℕ) → FracMech n (Fin m); reason: the member at m = 0 is never used: (3) is vacuous there since Opt = 0
--   - encoding: n machines → Fin n with [NeZero n]; reason: n ≥ 1
--   - encoding: a deterministic fractional mechanism on nonnegative inputs: x_ij(t) ∈ [0,1], Σ_i x_ij(t) = 1, payments P_i(t), truthfulness (1) for nonnegative true types, reports and opposing reports → FracMech n τ (total functions x, P on real matrices) with IsFeasibleOn and IsTruthfulOn imposed on the admissible inputs only (Nonneg, resp. IsGraphInput); values elsewhere are unconstrained; reason: Lean convention; the paper's mechanisms are exactly the restrictions of such pairs to the admissible inputs
--   - encoding: a graph input of MC_ℓ: the two endpoint values of every edge and the owner value of every self-loop, all nonnegative, and no other values → t : Fin n → CoreTask n ℓ → ℝ, nonnegative and 0 at every (machine, task) pair that is not incident (IsGraphInput); edges of Q{u,v} are encoded with u < v; reason: a machine's cost Σ_e t_ie x_ie is then its cost on its incident tasks; same inputs and same costs
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 1, p.9 (with eq. (3), p.4; Claim 10, App. A.4, p.26)

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric

set_option autoImplicit false

namespace FracTruthSched

/-- **Lemma 1 (Padding)** (Anastasiadis et al., arXiv:2611.06642v1, Lemma 1, p.9). Let
`R = (R_m)` be a family of deterministic truthful fractional mechanisms on `n` machines, one for every
finite number of tasks, with finite worst-case approximation ratio `ρ` against the integral optimum
(eq. (3), p.4). For every `ℓ ≥ 2` there is a truthful fractional mechanism `(x, P)` on the core tasks
of `MC_ℓ`, defined at all nonnegative real graph inputs, with `Mech_x(t) ≤ ρ C(t)` for every graph
input `t` (7), including inputs with `C(t) = 0`, satisfying (i) eligibility, (ii) unique zeros,
(iii) zero-type irrelevance and (iv) symmetry. Consequently, if `(x, P)` has approximation ratio
greater than `ρ′`, the original family also exceeds `ρ′` on some finite input with positive optimum.

**Formalization Note.** `R : (m : ℕ) → FracMech n (Fin m)` (the member at `m = 0` is never used);
`ρ` is any real satisfying (3), i.e. any bound on the ratio at positive-optimum inputs (the worst-case
ratio itself is one). The "Consequently" sentence is the clause that the **same** mechanism satisfies
(7) with every `ρ′` for which the family satisfies (3) (its contrapositive form; App. A.4, Claim 10:
a violation `Mech_x(t) > ρ′ C(t)` yields `m ≥ 1` and an input `s′` with `Opt(s′) > 0` and
`Mech_{R_m}(s′) > ρ′ Opt(s′)`). -/
theorem lemma_1 {n : ℕ} [NeZero n] (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (ρ : ℝ) (hρ : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ * opt t)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ M : FracMech n (CoreTask n ℓ),
      IsFeasibleOn IsGraphInput M ∧ IsTruthfulOn IsGraphInput M ∧
      (∀ t, IsGraphInput t → makespan M t ≤ ρ * C t) ∧
      (∀ ρ' : ℝ, (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
          makespan (R m) t ≤ ρ' * opt t) →
        ∀ t, IsGraphInput t → makespan M t ≤ ρ' * C t) ∧
      IsEligible M ∧ HasUniqueZeros M ∧ HasZeroTypeIrrelevance M ∧ IsClassSymmetric M := by sorry

end FracTruthSched

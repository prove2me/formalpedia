-- Prove2me | Theorems.Thm_NestedLogitNBR_nbr_scaled_feasible
-- name    : NestedLogitNBR.nbr_scaled_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:49:31.508111+00:00
-- url     : https://prove2.me/theorems/1d58c7ee-de1c-4c8b-8c02-8ab24b1c432c
-- title:
--   Theorem 7 — the nested-by-revenue LP solution scaled by the factor (6) is feasible for (3)
-- statement:
--   There are $m$ nests $M=\{1,\dots,m\}$, each offering products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}\ge 0$, and the products of every nest are ordered so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$. Nest $i$ has a dissimilarity parameter $\gamma_i\ge 0$, and $v_0\ge 0$ is the preference weight of choosing no nest. As in Section 4 of the paper the no-purchase weights inside the nests are $v_{i0}=0$, so $V_i(S)=\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$. The nested-by-revenue assortments are $N_{ij}=\{1,\dots,j\}$ for $j\in N_+=\{0,1,\dots,n\}$, with $N_{i0}=\emptyset$.
--
--   Let $(\hat x,\hat y)$ be an optimal solution of the linear program (4) whose candidate assortments are the nested-by-revenue assortments $\{N_{ij}:j\in N_+\}$:
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge V_i(N_{ij})^{\gamma_i}\big(R_i(N_{ij})-x\big)\ \ \forall j\in N_+,\ i\in M,
--   $$
--
--   and let
--
--   $$
--   \alpha=\max\Big\{1,\ \max_{i\in M,\ j=2,\dots,n}\Big\{\frac{R_i(N_{i,j-1})}{R_i(N_{ij})}\wedge\frac{R_i(N_{ij})}{R_i(N_{i,j-1})}\frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}}\Big\}\Big\}\tag{6}
--   $$
--
--   ($a\wedge b=\min\{a,b\}$). Then $(\alpha\hat x,\alpha\hat y)$ is feasible for the full linear program (3):
--
--   $$
--   v_0\,\alpha\hat x\ \ge\ \sum_{i\in M}\alpha\hat y_i,\qquad \alpha\hat y_i\ \ge\ V_i(S)^{\gamma_i}\big(R_i(S)-\alpha\hat x\big)\quad\text{for all } S\subseteq N,\ i\in M.
--   $$
--
--   By Theorem 1 of the paper, the best combination of nested-by-revenue assortments, which (4) computes with $1+m(1+n)$ constraints, therefore earns at least a fraction $1/\alpha$ of the optimal expected revenue of the nested logit assortment problem, even when the dissimilarity parameters exceed one and the problem is NP-hard.
--
--   Differences from the source:
--   - reading: α, the expression (6): max over i ∈ M, j = 2,…,n of the bracketed minimum → factor6 = max{1, (6)}, Lean's x/0 = 0 inside the terms, and 1 for n ≤ 1; reason: (6) is 0/0 on data the model allows (zero-weight padding, p. 7; zero revenues, as in the reduction of Theorem 5, p. 18) and the paper does not say what it is then; the bare maximum with x/0 = 0 makes the statement false (E1: nest 1 with γ=2, r=(0,0), v=(1,1), nest 2 with γ=0.01, r=(2,1), v=(1,1), v_0=1 satisfies every assumption of §4; all of nest 1's terms are 0/0, the Lean value of the bare maximum is 0.755, x̂ = 1, and (0.755 x̂, 0.755 ŷ) is infeasible for (3)); wherever every term is defined and some γ_i > 1, Lemma 14 gives (6) ≥ 1 so max{1, (6)} = (6); α ≥ 1 is necessary whenever x̂ > 0
--   - generalization: standing assumption of §4 (p. 16): γ_i > 1 for some i ∈ M → not assumed; every γ_i ≥ 0; reason: with α = max{1, (6)} the assumption is used only through Lemma 14 to get α ≥ 1, which the reading builds in; under the assumption the statement specializes to the paper's wherever (6) is defined
--   - reading: revenues r_ij with no stated sign → r_ij ≥ 0; reason: revenues are prices; the proof uses x̂ ≥ 0 and Σ_{k≤j} r_ik v_ik ≥ Σ_{k≤j−1} r_ik v_ik; with negative revenues the printed Theorem 7 fails on fully defined data (E2: nest 1 with γ=2, r=(−1,−2), v=(1,1), nest 2 with γ=0.01, r=(2,1), v=(1,1), v_0=1: every term of (6) is defined, (6) = 0.755, x̂ = 1, and (0.755 x̂, 0.755 ŷ) is infeasible for (3))
--   - reading: V_i(S)^{γ_i} (and (Σ_j v_ij z_ij)^{γ_i} in (7), (8)) at total weight 0 → 0 when the weight is 0, Real.rpow otherwise; reason: the paper uses V_i(∅)^{γ_i}(R_i(∅) − x̂) = 0 (p. 41) and an assortment of total weight 0 is never chosen (p. 7); Real.rpow gives 0^0 = 1 at γ_i = 0, which the model allows
--   - encoding: v_i0 = 0 (§4); products {1,…,n}; N_ij = {1,…,j}, j ∈ N_+; S_i ⊂ N; optimal solution of (4); R_i(∅) = 0 → prefWeight without v_i0; Fin n, 0-based; nbr j; every Finset (Fin n); FeasibleNBR with least x (IsOptimalNBR); x/0 = 0; reason: Lean conventions; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), Theorem 7, p. 21; factor (6), p. 19; proof App. A.1, pp. 41-43

import Mathlib
import Definitions.Def_NestedLogitNBR_IsOptimalNBR
import Definitions.Def_NestedLogitNBR_FeasibleFull
import Definitions.Def_NestedLogitNBR_factor6

namespace NestedLogitNBR

/-- **Theorem 7: the nested-by-revenue LP solution scaled by the factor (6) is feasible for (3).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), Theorem 7, p. 21: "Let `(x̂, ŷ)` be an optimal solution to problem (4) when we solve this
problem after replacing the collection of candidate assortments `{A_it : t ∈ T_i}` in the second
set of constraints with the nested-by-revenue assortments `{N_ij : j ∈ N_+}`. Then, using `α` to
denote the expression in (6), `(α x̂, α ŷ)` is a feasible solution to problem (3)."

Standing hypotheses (pp. 7, 16): `v_0 ≥ 0`, `v_ij ≥ 0`, revenues `r_ij ≥ 0` ordered
`r_i1 ≥ … ≥ r_in` in every nest, `γ_i ≥ 0`, `v_i0 = 0`. The factor `α` is (6), p. 19, read as `max{1, (6)}` (`factor6`).

**Formalization Note.** Problem (4) with the nested-by-revenue candidates is `FeasibleNBR` /
`IsOptimalNBR` (constraints for `N_i0 = ∅, N_i1, …, N_in`); problem (3) is `FeasibleFull`
(constraints for all `2^n` subsets). `V_i(S)^{γ_i}` is taken as `0` when `V_i(S) = 0`
(`nestAttraction`). The paper's standing assumption "`γ_i > 1` for some `i`" (Section 4, p. 16)
is not assumed: it serves only to make (6) at least `1` (Lemma 14), which `max{1, (6)}` builds
in; under it the two factors agree wherever (6) is defined. -/
theorem nbr_scaled_feasible {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (hv0 : 0 ≤ v0) (hv : ∀ i j, 0 ≤ v i j) (hr : ∀ i j, 0 ≤ r i j)
    (hord : ∀ i, Antitone (r i)) (hγ : ∀ i, 0 ≤ γ i)
    (x : ℝ) (y : Fin m → ℝ) (hopt : IsOptimalNBR v0 r v γ x y) :
    FeasibleFull v0 r v γ (factor6 r v γ * x) (fun i => factor6 r v γ * y i) := by sorry

end NestedLogitNBR

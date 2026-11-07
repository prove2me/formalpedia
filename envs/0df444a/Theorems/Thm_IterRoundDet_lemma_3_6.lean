-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_6
-- name    : IterRoundDet.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:41.516213+00:00
-- url     : https://prove2.me/theorems/b23603ad-4c37-4a45-8de6-30b9c2f28f83
-- title:
--   Lemma 3.6 with Lemma 3.8 — $g$ and $\Psi$ satisfy properties (i)–(iii) with $\alpha=14$; the exchange step
-- statement:
--   The regularizer $g$ and the objective $\Psi$ of (23) satisfy, for $(a,x)\in\mathcal R$ with components $A_1,\dots,A_q$:
--
--   1. $0\le g(a,x)\le 14d$;
--   2. if $(a,x)$ is not proportional, there are $i\ne j$ such that $(a,x+\varepsilon(\mathbf 1_i-\mathbf 1_j))$ is feasible and $\Psi(a,x+\varepsilon(\mathbf 1_i-\mathbf 1_j))\ge\Psi(a,x)$ for all sufficiently small $\varepsilon>0$;
--   3. at every proportional pair such that $x$ has a fractional coordinate, there is a nonzero direction $(v,w)$ such that $(a,x)\pm t(v,w)$ is feasible and, for all sufficiently small $t>0$,
--
--   $$\Psi(a+tv,x+tw)+\Psi(a-tv,x-tw)>2\Psi(a,x);$$
--
--   4. (Lemma 3.8) if $a_i/x_i>a_j/x_j$ for $i,j$ in the same component, then $(a,x+\varepsilon(\mathbf 1_i-\mathbf 1_j))\in\mathcal R$ and $\Psi(a,x+\varepsilon(\mathbf 1_i-\mathbf 1_j))>\Psi(a,x)$ for all sufficiently small $\varepsilon>0$.
--
--   Together these drive the continuous rounding walk to an integral $x$ with a loss of at most $14d$.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - reading: (ii): there are i, j → there are i ≠ j; reason: the printed move is an exchange of two elements; i = j would be empty. Lemma 3.8 gives it when ratios differ; a component with all ratios 0 gives it with equality
--   - generalization: Lemma 3.6, properties (i)–(iii) → also Lemma 3.8 (the strict exchange step) as a fourth conjunct; reason: Lemma 3.8 is the printed proof of (ii), on the same page; the printed properties are conjuncts, so the item specializes to the lemma; the title names Lemma 3.8
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.6, p.16, properties (i)–(iii), p.15; Lemma 3.8, p.16

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Regularizer

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.6, pp.15–16, with Lemma 3.8, p.16. The regularizer `g` and the regularized objective `Ψ` of (23)
satisfy properties (i)–(iii) with `α = 14`:
(i) `0 ≤ g(a, x) ≤ 14d`; (ii) if `(a, x) ∈ R` is not proportional there are `i, j` such that `(a, x + ε(1_i − 1_j))` is feasible and
`Ψ(a, x + ε(1_i − 1_j)) ≥ Ψ(a, x)` for all sufficiently small `ε > 0`; (iii) at every proportional pair such that `x` has a
fractional coordinate there is a nonzero direction `(v, w)` such that `(a, x) ± t(v, w)` is feasible and
`Ψ(a + tv, x + tw) + Ψ(a − tv, x − tw) > 2Ψ(a, x)` for all sufficiently small `t > 0`. Lemma 3.8 (exchange step): if
`a_i/x_i > a_j/x_j` for `i, j` in the same component, then `(a, x + ε(1_i − 1_j)) ∈ R` and the strict inequality holds.

**Formalization Note.** (ii) asks `i ≠ j`, since the printed move is an exchange of two elements and at `i = j` it would be
empty. The components are the blocks of the partition `π` of Lemma 2.6. `1_i` is `ind {i}`. -/
theorem lemma_3_6 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c)
    {M : Matroid (Fin n)} (hM : M.E = Set.univ) {a x : Fin n → ℝ} (hax : Feasible c M a x)
    {π : Finpartition (fractional x)} (hπ : IsFacePartition M x π) :
    (0 ≤ gReg d a x ∧ gReg d a x ≤ 14 * d) ∧
    (¬ IsProportional a x π → ∃ i j : Fin n, i ≠ j ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Feasible c M a (x + ε • (ind {i} - ind {j})) ∧
      Psi c d a x ≤ Psi c d a (x + ε • (ind {i} - ind {j}))) ∧
    (IsProportional a x π → (fractional x).Nonempty →
      ∃ v w : Fin n → ℝ, (v ≠ 0 ∨ w ≠ 0) ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
        Feasible c M (a + t • v) (x + t • w) ∧ Feasible c M (a - t • v) (x - t • w) ∧
        2 * Psi c d a x < Psi c d (a + t • v) (x + t • w) + Psi c d (a - t • v) (x - t • w)) ∧
    (∀ s ∈ π.parts, ∀ i ∈ s, ∀ j ∈ s, a j / x j < a i / x i →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        Feasible c M a (x + ε • (ind {i} - ind {j})) ∧
        Psi c d a x < Psi c d a (x + ε • (ind {i} - ind {j}))) := by sorry

end IterRoundDet

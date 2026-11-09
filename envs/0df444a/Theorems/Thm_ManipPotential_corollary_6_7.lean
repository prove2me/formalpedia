-- Prove2me | Theorems.Thm_ManipPotential_corollary_6_7
-- name    : ManipPotential.corollary_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:54:41.282867+00:00
-- url     : https://prove2.me/theorems/d70f8dac-2cfe-418c-bd0f-362e3dd5eb0f
-- title:
--   Corollary 6.7 — positive cyclic share with external rankings (11)
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, $\delta = (m-2)/(\lambda^6 + m - 2)$, and let $g$ satisfy the axioms of Lemma 6.2. For every rational profile $P = (x, y) \ge 0$, with cyclic coordinates $x_i = P_{\ell_i}$, external coordinates $y$, and $X = \sum_{i=1}^m x_i > 0$: if $g(P) = c_j$, then
--   $$
--   x_j \ \ge\ \delta X - \lambda (1 - \delta)\, \|y\|_1 . \qquad (11)
--   $$
--   The bound of Lemma 6.6 survives the presence of external rankings, up to a loss proportional to their total weight.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - generalization: λ > 1, a standing assumption from the remark after Lemma 6.6 (p.30, "for the rest of the proof, we can assume λ > 1") → no λ > 1 hypothesis: every K ∈ ℕ, so λ = K + 1 ≥ 1; reason: at K = 0 no g satisfies the axioms (remark after Lemma 6.6, item lambda_one_impossible), so the extra instances are vacuous and the statement specializes to the source
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: ‖y‖₁ of the external coordinates → the sum of |P_s| over the rankings s different from every ℓ_j; reason: same quantity
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Corollary 6.7, Eq. (11), p.30

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycTotal
import Definitions.Def_ManipPotential_extNorm
import Definitions.Def_ManipPotential_delta

namespace ManipPotential

/-- Corollary 6.7 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Corollary 6.7, Eq. (11), p.30), with `λ = K + 1`: for every rational
profile `P = (x, y) ≥ 0` with `X = ∑_i x_i > 0`, if `g(P) = c_j` then
`x_j ≥ δ X − λ (1 − δ) ‖y‖₁`. -/
theorem corollary_6_7 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (P : Ranking m → ℚ) (hP : 0 ≤ P) (hX : 0 < cycTotal P) (j : Fin m)
    (hj : g P = j) :
    delta m K * cycTotal P - ((K : ℚ) + 1) * (1 - delta m K) * extNorm P ≤ P (ell j) := by sorry

end ManipPotential

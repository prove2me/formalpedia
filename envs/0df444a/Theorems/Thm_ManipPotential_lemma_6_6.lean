-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_6
-- name    : ManipPotential.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:54:35.028036+00:00
-- url     : https://prove2.me/theorems/5cd06d97-1707-40c7-b263-6aef24ca1933
-- title:
--   Lemma 6.6 — positive cyclic share of the winning ranking, (8) and (9)
-- statement:
--   Let $m \ge 3$, $\lambda = K + 1$, and let $g$ satisfy the axioms of Lemma 6.2.
--
--   1. For every $i \in [m]$ and rationals $x_i > 0$, $x_{i-1} \ge 0$: if $g(x_i \ell_i + x_{i-1} \ell_{i-1}) = c_{i-1}$, then
--   $$ (m - 2)\, x_i \le \lambda^5 x_{i-1}. \qquad (8) $$
--   2. For every $x \in \mathbb Q^m_{\ge 0}$ with $X = \sum_{j=1}^m x_j > 0$: if $g(xL) = c_i$, then
--   $$ \frac{x_i}{X} \ \ge\ \delta := \frac{m - 2}{\lambda^6 + m - 2}, \qquad (9) $$
--   and $\delta > 0$.
--
--   So on an L-profile the winning ranking always carries a share of the total weight bounded below by a constant depending only on $\lambda$ and $m$.
--
--   Differences from the source:
--   - generalization: g is the rule on rational profiles constructed from f in Lemma 6.2 → any g satisfying the three axioms of Lemma 6.2 with λ = K + 1; reason: the proof uses only these axioms, and the g of Lemma 6.2 satisfies them
--   - encoding: g : ℚ^{m!}_{≥0} \ {0} → C → a total g : (Ranking m → ℚ) → Fin m, queried (here and in the axioms) only at nonnegative nonzero vectors; reason: Lean convention; values outside the domain never matter
--   - encoding: candidates c_1…c_m, indices mod m, ℓ_j and r_j as printed → Fin m (0-based), ℓ_j : c ↦ j − c and r_j : c ↦ c − j as permutations to positions; reason: Lean convention; same rankings
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.6, Eqs. (8)–(9), p.29

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_delta

namespace ManipPotential

/-- Lemma 6.6 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.6, Eqs. (8)–(9), p.29), with `λ = K + 1`: (8) for every `i` and
rationals `x_i > 0`, `x_{i−1} ≥ 0`, if `g(x_i ℓ_i + x_{i−1} ℓ_{i−1}) = c_{i−1}` then
`(m − 2) x_i ≤ λ⁵ x_{i−1}`; (9) for every `x ∈ ℚ^m_{≥0}` with `X = ∑_j x_j > 0`, if `g(xL) = c_i`
then `x_i / X ≥ δ = (m − 2)/(λ⁶ + m − 2)`, and `δ > 0`. -/
theorem lemma_6_6 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    (∀ (i : Fin m) (xi xim : ℚ), 0 < xi → 0 ≤ xim →
      g (xi • unitVec (ell i) + xim • unitVec (ell (i - 1))) = i - 1 →
      ((m : ℚ) - 2) * xi ≤ ((K : ℚ) + 1) ^ 5 * xim) ∧
    (∀ x : Fin m → ℚ, 0 ≤ x → 0 < ∑ j, x j → ∀ i : Fin m, g (cycL x) = i →
      delta m K ≤ x i / ∑ j, x j) ∧
    0 < delta m K := by sorry

end ManipPotential

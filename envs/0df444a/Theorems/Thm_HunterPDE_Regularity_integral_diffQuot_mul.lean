-- Prove2me | Theorems.Thm_HunterPDE_Regularity_integral_diffQuot_mul
-- name    : HunterPDE.Regularity.integral_diffQuot_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:26:34.81385+00:00
-- url     : https://prove2.me/theorems/613f85b8-a8ce-4173-9431-35520a6a4fec
-- title:
--   Proposition 4.52 (2) — discrete integration by parts for difference quotients
-- statement:
--   Let $1 \le p \le \infty$ and let $p'$ be the conjugate exponent, $1/p + 1/p' = 1$. If $u \in L^p(\mathbb{R}^n)$, $v \in L^{p'}(\mathbb{R}^n)$ and $h \ne 0$, then
--   $$\int_{\mathbb{R}^n} (D_i^h u)\, v \, dx = -\int_{\mathbb{R}^n} u\, (D_i^{-h} v)\, dx .$$
--
--   This is the discrete analogue of integration by parts, used to move a difference quotient from the solution onto the test function.
--
--   **Formalization Note.** The printed statement of Proposition 4.52 (2) has $D_i^h v$ on the right-hand side; the book's own proof on p. 125 ends with $-\int u\,(D_i^{-h} v)\,dx$, which is the correct identity and is the one stated here. The exponents are `p q : ℝ≥0∞` with `p.HolderConjugate q`. Coordinates are 0-based.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 124, Proposition 4.52 (2) (sign as in the proof, p. 125)

import Mathlib
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity

/-- Proposition 4.52 (2) of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 124 (discrete
integration by parts): if `u ∈ Lᵖ(ℝⁿ)` and `v ∈ L^{p'}(ℝⁿ)`, where `1 ≤ p ≤ ∞` and `p'` is the
Hölder conjugate exponent (`1/p + 1/p' = 1`), then
`∫ (D_i^h u) v dx = −∫ u (D_i^{−h} v) dx`.
The printed statement has `D_i^h v` on the right; the book's own proof (p. 125) ends with
`−∫ u (D_i^{−h} v) dx`, which is the correct identity and is what is stated here. -/
theorem integral_diffQuot_mul {n : ℕ} (i : Fin n) (h : ℝ) (hh : h ≠ 0) (p q : ℝ≥0∞)
    (hpq : p.HolderConjugate q) (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : MemLp u p volume) (hv : MemLp v q volume) :
    ∫ x, diffQuot i h u x * v x = -∫ x, u x * diffQuot i (-h) v x := by sorry

end HunterPDE.Regularity

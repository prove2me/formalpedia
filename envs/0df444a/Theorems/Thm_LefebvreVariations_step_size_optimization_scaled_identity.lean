-- Prove2me | Theorems.Thm_LefebvreVariations_step_size_optimization_scaled_identity
-- name    : LefebvreVariations.step_size_optimization_scaled_identity
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:19:00.590313+00:00
-- url     : https://prove2.me/theorems/170bd04e-c627-4419-a0d8-94bb274161a7
-- title:
--   Lefebvre's variations, No. 251 — on a theme by Beck and Teboulle: the optimal mirror-descent step size when the Hessian bound is a multiple of the identity
-- statement:
--   Let $d\ge0$, $c,\sigma,L>0$, let $b=(1,\dots,1)\in\mathbb R^d$ and $D=L^2I_d$. Then
--   $$
--   \min_{z\in\mathbb R^d_{++}}\ \frac{c+(2\sigma)^{-1}z^{\top}Dz}{b^{\top}z}\ =\ \sqrt{\frac{2c}{\sigma\,b^{\top}D^{-1}b}},
--   $$
--   the minimum is attained at $z^*=\sqrt{\dfrac{2c\sigma}{b^{\top}D^{-1}b}}\;D^{-1}b$, and $z^*$ has all coordinates positive.
--
--   This is the case $D=L^2I$, $b=e$ (the one used in the paper, $D=L_f^2I$) of the optimal step-size formula of Beck and Teboulle for mirror descent, which the platform lists as open for every symmetric positive definite $D$ and every $b>0$ with $D^{-1}b>0$.
--
--   **Formalization Note** The matrix is `D = (l ^ 2) • 1 : Matrix (Fin d) (Fin d) ℝ` and `b = fun _ => 1`; the statement keeps the parent's three conclusions (`IsLeast` of the set of ratio values, positivity of `z*`, and the value at `z*`). For `d = 0` the empty vector gives the ratio `c / 0 = 0` and the right-hand side is `√0 = 0`, so the statement holds trivially there.
--
--   **Why this is a variation.** A variation on the open platform problem BeckTeboulleMD.EMDA.step_size_optimization (the minimum of [c + (2σ)^{-1} zᵀDz]/(bᵀz) over z > 0 is √(2c/(σ bᵀD⁻¹b))), played at the diagonal case D = L² I, b = (1,...,1) that the source paper actually uses, with the parent's three conclusions restated verbatim, not imported. The statement for a general positive definite D with D⁻¹b > 0 stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. Beck and M. Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Operations Research Letters 31 (2003) 167-175, Section 4, Proposition 4.1 (cited from memory; page numbers not verified). The scaled-identity case is elementary (Cauchy-Schwarz ||z||^2 >= (sum z)^2/d, then AM-GM); checked by hand: with t = sqrt(2 c sigma L^2/d) the value at z* = t/L^2 * (1,...,1) is sqrt(2 c L^2/(sigma d)).

import Mathlib

set_option autoImplicit false

open Matrix

namespace LefebvreVariations

/-- The case `D = L² I`, `b = (1, …, 1)` of `BeckTeboulleMD.EMDA.step_size_optimization` (Beck–Teboulle, Proposition 4.1;
the only case used in the paper, `D = L_f² I`, `b = e`): for `c, σ, L > 0` in any dimension `d` (for `d = 0` both sides are
`0` by `a / 0 = 0`), the minimum over `z ∈ ℝ^d_{++}` of `[c + (2σ)⁻¹ zᵀDz] / (bᵀz)` is `√(2c / (σ bᵀD⁻¹b))`, attained
at `z* = √(2cσ / bᵀD⁻¹b) · D⁻¹ b`.
Source: A. Beck, M. Teboulle, *Mirror descent and nonlinear projected subgradient methods for convex optimization*,
Oper. Res. Lett. 31 (2003), §4 (cited from memory); elementary (the Cauchy–Schwarz inequality `‖z‖² ≥ (Σz)²/d`
plus AM–GM). -/
theorem step_size_optimization_scaled_identity {d : ℕ} (c σ l : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hl : 0 < l)
    (b : Fin d → ℝ) (hb : b = fun _ => 1) (D : Matrix (Fin d) (Fin d) ℝ)
    (hD : D = (l ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    IsLeast {v : ℝ | ∃ z : Fin d → ℝ, (∀ i, 0 < z i) ∧
        v = (c + (2 * σ)⁻¹ * (z ⬝ᵥ (D *ᵥ z))) / (b ⬝ᵥ z)}
      (Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b))))) ∧
    (∀ i, 0 < (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)) i) ∧
    (c + (2 * σ)⁻¹ * ((Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)) ⬝ᵥ
        (D *ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b))))) /
        (b ⬝ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b))) =
      Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b)))) := by
  sorry

end LefebvreVariations

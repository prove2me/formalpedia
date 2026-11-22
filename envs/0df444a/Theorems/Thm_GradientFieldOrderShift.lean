-- Prove2me | Theorems.Thm_GradientFieldOrderShift
-- name    : GradientFieldOrderShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:09:36.104061+00:00
-- url     : https://prove2.me/theorems/6fc9cf14-f974-43fc-9ebf-45de17b1ee4b
-- title:
--   Gradient Field Order Shift: Gradient Field Order Shift
-- statement:
--   The classical gradient field is the Riesz transport of the Frechet derivative, and the
--   order-`n` jet of the gradient field is ISOMETRIC to the order-`(n+1)` jet of the scalar.
--
--   For an open `U` and a function `v` that is `C^∞` on `U`, four facts:
--
--   * (1) the FACTORIZATION `Dv = J⁻¹ ∘ D¹v`, where `J⁻¹` is the inverse Riesz map
--     `(Plane →L[ℝ] ℝ) ≃ₗᵢ Plane`.  This is needed at all because the order-shift proposition
--     differentiates `D¹v : Plane → (Plane →L[ℝ] ℝ)`, which takes values in the DUAL of the plane,
--     whereas the classical gradient field `Dv : Plane → Plane` takes values in the plane itself,
--     and this development keeps the two apart;
--   * (2) the gradient field inherits `C^∞` on `U` from `v`;
--   * (3) the ONE-POINT order shift `‖D^n (Dv) x‖ = ‖D^(n+1) v x‖`.  This one needs no domain and no
--     regularity: it follows from (1) alone, since post-composition with the Riesz isometry and the
--     order-shift isometry each preserve the norm of an iterated derivative, so it is stated for
--     every `x : Plane`;
--   * (4) the TWO-POINT order shift, the same identity on a difference of jets at two points of `U`.
--     A Holder seminorm is a two-point difference, so (3) does not give it: the two isometries have
--     to be moved outside the difference, which needs them to be LINEAR as well as norm-preserving,
--     and moving the Riesz map outside the iterated derivative at a point of `U` needs `ContDiffAt`
--     there -- which is why this clause, unlike (3), is restricted to `U`.
--
--   Every clause is an EQUALITY: no constant is lost in the passage between a scalar function and its
--   gradient field.  This is the bridge the Schauder bootstrap of the paper's lem:noncritical crosses
--   in both directions -- it carries its inductive hypothesis on the scalar `v` but applies its
--   composition estimate and its divergence-form input to the gradient field `Dv`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/GradientFieldOrderShift.lean#L28-L81
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/GradientFieldOrderShift.lean#L28-L81

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_GradientFieldOrderShift
set_option autoImplicit false

theorem GradientFieldOrderShift (U : Set Plane) (v : Plane → ℝ)
    (hUo : IsOpen U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    gradient v
        = (fun T : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm T) ∘ fderiv ℝ v
      ∧ ContDiffOn ℝ (⊤ : ℕ∞) (gradient v) U
      ∧ (∀ (n : ℕ) (x : Plane),
          ‖iteratedFDeriv ℝ n (gradient v) x‖ = ‖iteratedFDeriv ℝ (n + 1) v x‖)
      ∧ (∀ (n : ℕ), ∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ n (gradient v) x - iteratedFDeriv ℝ n (gradient v) y‖
            = ‖iteratedFDeriv ℝ (n + 1) v x - iteratedFDeriv ℝ (n + 1) v y‖) := by sorry

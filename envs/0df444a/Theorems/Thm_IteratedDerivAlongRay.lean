-- Prove2me | Theorems.Thm_IteratedDerivAlongRay
-- name    : IteratedDerivAlongRay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:09:44.693854+00:00
-- url     : https://prove2.me/theorems/21b7c45f-fa54-4771-a56b-3569c07c7528
-- title:
--   Iterated Deriv Along Ray: Iterated Deriv Along Ray
-- statement:
--   Restriction to a ray converts diagonal iterated Frechet derivatives into
--   one-variable iterated derivatives:  if `u` is `C^j` on an open set `U` and
--   `x₀ + t • e ∈ U`, then the `j`-th derivative at `t` of the one-variable function
--   `s ↦ u (x₀ + s • e)` equals the `j`-th Frechet derivative of `u` at `x₀ + t • e`
--   evaluated on `j` copies of `e`.
--
--   Mathlib's `Analysis/Calculus/LineDeriv/` covers first derivatives only, and all of
--   its Taylor remainder bounds are one-dimensional, so this transfer lemma is what lets
--   higher-order information about `u` be extracted along rays.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IteratedDerivAlongRay.lean#L12-L60
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IteratedDerivAlongRay.lean#L12-L60

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
set_option autoImplicit false

theorem IteratedDerivAlongRay (U : Set Plane) (hU : IsOpen U) (u : Plane → ℝ) (j : ℕ)
    (hu : ContDiffOn ℝ (j : ℕ∞) u U) (x₀ e : Plane) (t : ℝ) (ht : x₀ + t • e ∈ U) :
    iteratedDeriv j (fun s : ℝ => u (x₀ + s • e)) t
      = iteratedFDeriv ℝ j u (x₀ + t • e) (fun _ => e) := by sorry

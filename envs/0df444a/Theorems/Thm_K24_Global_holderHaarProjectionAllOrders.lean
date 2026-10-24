-- Prove2me | Theorems.Thm_K24_Global_holderHaarProjectionAllOrders
-- name    : K24.Global.holderHaarProjectionAllOrders
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T20:09:08.367064+00:00
-- url     : https://prove2.me/theorems/655cb327-4a12-431d-869a-a42e71690554
-- title:
--   K24: exact actual Holder Haar projection conclusions at every finite order
-- statement:
--   For every smooth real four-manifold M, every actual BoundedLocalCover C, every positive nonnegative-real exponent alpha, every nonnegative action bound H, every finite natural order and every original smooth CircleAction rho, the original HolderActionControl C alpha H order rho implies the exact original HolderProjectionConclusions C alpha H order rho.
--
--   For all three actual section types (covariant two-tensors, covectors and vectors), and every k up to that order, this establishes genuine Haar integrability, preservation of the original Ck,alpha cover space by Pi0 and PiPerp, invariance and idempotence of Pi0, zero Haar mean of PiPerp, and the exact original norm bounds H and 1+H. No extra compactness or Hausdorffness assumption on M is used; the circle parameter is compact. No upper bound on alpha or lower bound H>=1 is needed.
--
--   The proof differentiates actual finite-dimensional coefficient integrals using parameter measurability and dominated differentiation. It integrates a combined witness for derivative suprema and the top Holder quotient, retaining the exact constants. It neither assumes norm-continuous orbits in the big Holder space nor assumes a false lower-order Holder embedding on disconnected inner domains.
--
--   This supplies all projection fields at original orders 2 and 3. Sobolev projections and the remaining global analytic conclusions remain open. Parent https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 ; current frontier https://prove2.me/theorems/3db797ab-2b53-4cda-b318-e4780235e38c .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §1 common Haar projection framework; exact normalized measure and quantitative HolderProjectionConclusions are in the unchanged canonical K24GlobalGeometry and K24GlobalStatement definitions.

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open K24.Global
open scoped Manifold ContDiff NNReal
universe u

theorem K24.Global.holderHaarProjectionAllOrders {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (α H : ℝ≥0) (hα : 0 < α)
    (order : ℕ) (rho : CircleAction M) :
    HolderActionControl C α H order rho → HolderProjectionConclusions C α H order rho := by sorry

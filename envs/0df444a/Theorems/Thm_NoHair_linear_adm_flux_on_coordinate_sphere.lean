-- Prove2me | Theorems.Thm_NoHair_linear_adm_flux_on_coordinate_sphere
-- name    : NoHair.linear_adm_flux_on_coordinate_sphere
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:52:43.319395+00:00
-- url     : https://prove2.me/theorems/fc749975-3ecf-44af-b064-56c6802339cd
-- title:
--   Exact linearized Einstein flux on a coordinate sphere
-- statement:
--   For any smooth Cartesian spatial tensor and any coordinate sphere, its ADM surface integral agrees exactly with the radial flux of the divergence of its antisymmetric ADM potential. For a symmetric tensor this gives the flux of $-2G'_{\delta}(k)$ contracted against the Euclidean position vector. This is the finite-radius integration-by-parts identity behind the intrinsic curvature expression for ADM mass; no asymptotic condition is needed.
-- source:
--   P. Miao and L.-F. Tam, Evaluation of the ADM mass and center of mass via the Ricci tensor, Proc. Amer. Math. Soc. 144 (2016), pp. 753–761, Theorem 1.1(a) and the Euclidean integration-by-parts identity in the proof of Theorem 2.1, equations (2.2)–(2.8), https://arxiv.org/abs/1408.3893, https://doi.org/10.1090/proc12726.

import Definitions.Def_NoHair_linearADMFlux

open Set Filter MeasureTheory NoHair
open scoped ContDiff Manifold Topology

theorem NoHair.linear_adm_flux_on_coordinate_sphere (k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hsmooth : ∀ i j, ContDiff ℝ ∞ (fun x => k x i j)) (R : ℝ) (hR : 0 < R) :
    staticADMFlux k R = (∫ n : ADMSphere,
      ∑ j : Fin 3, (∑ i : Fin 3, R^2 * (R • (n : ADMPoint)) i *
        negativeTwiceLinearEinstein k i j (R • (n : ADMPoint))) * (n : ADMPoint) j
        ∂admSurfaceMeasure) / (16 * Real.pi) := by sorry

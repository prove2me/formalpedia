-- Prove2me | Theorems.Thm_NoHair_static_linearized_einstein_trace_identity
-- name    : NoHair.static_linearized_einstein_trace_identity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T08:21:26.16572+00:00
-- url     : https://prove2.me/theorems/34d7faa5-7540-4dc1-bcc9-8489b83c4ef8
-- title:
--   Trace reversal of the linearized static vacuum equations
-- statement:
--   For a smooth static lapse $N$ and symmetric spatial metric $h$, put $A=\mathrm{Ric}'_\delta(h)-\partial^2N$ and $k=h+2(N-1)\delta$. The exact pointwise identity $-2G'_\delta(k)=-2A+\delta(\operatorname{tr}A-\Delta N)$ gives every component of the ADM curvature current. The Cartesian formulas also give the identity for arbitrary component arrays in the stated index order.
-- source:
--   P. Miao and L.-F. Tam, Evaluation of the ADM mass and center of mass via the Ricci tensor, Proc. Amer. Math. Soc. 144 (2016), pp. 753–761, Theorem 1.1(a) and the Euclidean integration-by-parts identity in the proof of Theorem 2.1, equations (2.2)–(2.8), https://arxiv.org/abs/1408.3893, https://doi.org/10.1090/proc12726. For the time and spatial Ricci equations, see equations (5.4) and (5.5) of P. T. Chruściel, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf.

import Definitions.Def_NoHair_staticCartesianRicci

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.static_linearized_einstein_trace_identity (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) (hN : ContDiffAt ℝ ∞ N x)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (i j : Fin 3) :
    negativeTwiceLinearEinstein (lapseCorrectedADMMetric N h) i j x =
      -2 * staticPrincipalRicci N h i j x + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j *
        ((∑ l : Fin 3, staticPrincipalRicci N h l l x) - flatLapseLaplacian N x) := by sorry

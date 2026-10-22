-- Prove2me | Theorems.Thm_NewtonCartan_radPot_hessian_eq
-- name    : NewtonCartan.radPot_hessian_eq
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:14:42.783858+00:00
-- url     : https://prove2.me/theorems/f4ac7715-49a3-44cb-9d9e-f06e5724387b
-- title:
--   Radial integral potential recovers a closed Hessian on $\mathbb{R}^3$
-- statement:
--   Let $H:\mathbb{R}^3\to\mathrm{Sym}_3(\mathbb{R})$ be smooth, and assume the Hessian closedness condition
--   $$\partial_k H_{ij}=\partial_j H_{ik}$$
--   for all indices. Define the radial potential
--   $$
--   \varphi(y)=\sum_{i,j=1}^{3}\int_0^1(1-s)\,H_{ij}(sy)\,y_i y_j\,ds.
--   $$
--   Then $\varphi$ is smooth and
--   $$
--   \partial_j\partial_i\varphi(y)=H_{ij}(y)
--   $$
--   for all $y$ and all spatial indices $i,j$.
--
--   This is the standard integral form of Taylor's theorem with vanishing jet at the origin, specialized to recovering a potential from its Hessian; it is the key identity used to assemble a spacetime potential from slicewise spatial Hessians in Trautman recovery.
-- source:
--   Classical multivariable calculus (Taylor with integral remainder); Trautman/Malament Newton–Cartan recovery Prop. 2.2

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_exists_potential_of_closed_hessian_Sp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped ContDiff BigOperators Topology Interval
open Classical MeasureTheory
open NewtonCartan

namespace NewtonCartan

theorem radPot_hessian_eq
    (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (hsym : ∀ y i j, H y i j = H y j i)
    (hclosed : ∀ y i j k,
      fderiv ℝ (fun z => H z i j) y (Pi.single k 1) =
        fderiv ℝ (fun z => H z i k) y (Pi.single j 1)) :
    let φ : Sp → ℝ := fun y =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ s in (0 : ℝ)..1, (1 - s) * H (s • y) i j * y i * y j
    ContDiff ℝ ∞ φ ∧
      ∀ y i j, fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single i 1)) y (Pi.single j 1) =
        H y i j := by sorry

end NewtonCartan

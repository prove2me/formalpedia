-- Prove2me | Theorems.Thm_IDivGeom_ExpFam_eq_3_18
-- name    : IDivGeom.ExpFam.eq_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:23.288884+00:00
-- url     : https://prove2.me/theorems/884ca1ef-ef14-46b3-8f75-e5589dddde70
-- title:
--   (3.18) — A_R is convex and F is a finite convex function on A_R
-- statement:
--   Let $f_1,\dots,f_k$ be real-valued measurable functions on $(X,\mathcal X)$ and $R$ a PD. Let $\mathcal E(a_1,\dots,a_k)$ be the set of PD's $P$ with $\int f_i\,dP=a_i$, $i=1,\dots,k$, let $A_R$ be the set of $(a_1,\dots,a_k)\in E^k$ for which $\mathcal E(a_1,\dots,a_k)$ contains some $P$ with $I(P\|R)<\infty$, and let
--   $$F(a_1,\dots,a_k)=\inf_{P\in\mathcal E(a_1,\dots,a_k)} I(P\|R).$$
--   Then $A_R$ is a convex set, and $F$ is a finite valued convex function on $A_R$.
--
--   The function $F$ is the value of the minimum-discrimination problem as a function of the constraint levels; its convexity is what produces the supporting hyperplane (3.19) at interior points.
--
--   **Formalization Note** The page prints $I(P\|Q)$ in (3.18); $Q$ is not defined at that point, $A_R$ is defined through $I(P\|R)$, and the proof uses $I(P_n\|R)\to F(a_1,\dots,a_k)$, so the reference measure is $R$. $F$ is an infimum in $[0,\infty]$; the statement asserts that it is finite on $A_R$ and that its real value is convex on $A_R$. The constraint $\int f_i\,dP=a_i$ includes $P$-integrability of $f_i$.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 157 (PDF 12), (3.18), proof of Theorem 3.3

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

theorem eq_3_18 {X : Type*} [MeasurableSpace X]
    (k : ℕ) (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i))
    (R : Measure X) [IsProbabilityMeasure R] :
    Convex ℝ (finiteSet f R) ∧ (∀ a ∈ finiteSet f R, valueFn f R a ≠ ⊤) ∧
      ConvexOn ℝ (finiteSet f R) (fun a => (valueFn f R a).toReal) := by sorry

end IDivGeom.ExpFam

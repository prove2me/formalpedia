-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_oddWindow_triple_integrable
-- name    : OAI.TriangularHilbert.Heat.oddWindow_triple_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:59:06.47426+00:00
-- url     : https://prove2.me/theorems/4d59728c-1332-45be-bfec-694db07c71c7
-- title:
--   Integrability of a triple odd-window product on the plane
-- statement:
--   The odd window is $\omega_s(t)=\frac{t}{\sqrt s}\phi_s(t)$ and the signed kernel is $\kappa_s(t)=\frac{t^3/27-ts/3}{s\sqrt s}\phi_{3s}(t)$, with $\phi_\sigma$ the centred Gaussian density of variance $\sigma$. For $s>0$ and $a,b,c\in\mathbb R$, the function
--   $$
--   (z_1,z_2)\longmapsto\omega_s(a-z_1)\,\omega_s(b-z_2)\,\omega_s(c+z_1+z_2)
--   $$
--   is integrable on $\mathbb R^2$.
--
--   This is needed to evaluate the triple convolution of odd windows, which produces the signed kernel.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/SignedExpansion.lean#L27-L45

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators

theorem OAI.TriangularHilbert.Heat.oddWindow_triple_integrable {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) := by sorry

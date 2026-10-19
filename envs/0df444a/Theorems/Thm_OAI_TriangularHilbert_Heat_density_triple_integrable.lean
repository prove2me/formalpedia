-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_density_triple_integrable
-- name    : OAI.TriangularHilbert.Heat.density_triple_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:56:59.248001+00:00
-- url     : https://prove2.me/theorems/d9f052ac-9b3f-42be-b5a6-ed42d5ea38a4
-- title:
--   Integrability of a triple Gaussian product on the plane
-- statement:
--   Let $\phi_\sigma$ be the centred Gaussian density of variance $\sigma$. For $s,t,v>0$ and $a,b,c\in\mathbb R$, the function
--   $$
--   (z_1,z_2)\longmapsto\phi_s(a-z_1)\,\phi_t(b-z_2)\,\phi_v(c+z_1+z_2)
--   $$
--   is integrable on $\mathbb R^2$.
--
--   The three Gaussians correspond to the three centres of the triangle constrained by a linear relation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GaussianTriple.lean#L10-L24

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
open MeasureTheory

theorem OAI.TriangularHilbert.Heat.density_triple_integrable {s t v : ℝ} (hs : 0 < s) (ht : 0 < t) (hv : 0 < v) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) := by sorry

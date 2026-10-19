-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_intInterval_weighted_le
-- name    : OAI.TriangularHilbert.intInterval_weighted_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:14:38.030851+00:00
-- url     : https://prove2.me/theorems/21115ff2-590d-47a2-a124-36e205849325
-- title:
--   Radially decreasing averages are bounded by the maximal function
-- statement:
--   Let $D\subset\mathbb Z$ be finite, $f\ge0$ on $D$, $n\in\mathbb Z$, and let $g:\mathbb N\to\mathbb R$ be nonnegative and nonincreasing. Let $R=\max_{m\in D}|m-n|$. Then
--   $$
--   \sum_{m\in D}f(m)\,g(|m-n|)\le\mathrm{intMax}(D,f,n)\sum_{|m-n|\le R}g(|m-n|).
--   $$
--
--   Averages against a radially decreasing kernel are controlled by the centred maximal function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GaussianMax.lean#L44-L74

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax

open OAI OAI.TriangularHilbert
open scoped BigOperators

theorem OAI.TriangularHilbert.intInterval_weighted_le (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) (hdec : ∀ r, g (r+1) ≤ g r) :
    (∑ m ∈ D, f m*g (m-n).natAbs) ≤
      intMax D f n * ∑ m ∈ intInterval n (supportRadius D n), g (m-n).natAbs := by sorry

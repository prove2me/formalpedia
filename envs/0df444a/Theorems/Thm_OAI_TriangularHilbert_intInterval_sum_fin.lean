-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_intInterval_sum_fin
-- name    : OAI.TriangularHilbert.intInterval_sum_fin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:13:56.733348+00:00
-- url     : https://prove2.me/theorems/7f74f19b-d308-4c42-abb7-89aded649001
-- title:
--   Reindexing sums over integer intervals
-- statement:
--   For an integer $n$, a radius $N\in\mathbb N$ and $f:\mathbb Z\to\mathbb R$,
--   $$
--   \sum_{m=n-N}^{n+N}f(m)=\sum_{i=0}^{2N}f(n-N+i).
--   $$
--
--   Sums over the integer interval of radius $N$ around $n$ are rewritten as sums over $\{0,\dots,2N\}$. This matches the form of Riemann sums of Gaussian densities on arithmetic progressions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GaussianMax.lean#L25-L42

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

theorem OAI.TriangularHilbert.intInterval_sum_fin (n : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    (∑ m ∈ intInterval n N, f m) = ∑ i : Fin (2*N+1), f (n-(N:ℤ)+(i:ℕ)) := by sorry

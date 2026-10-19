-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_finite_disjoint_selection
-- name    : OAI.TriangularHilbert.finite_disjoint_selection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:11:42.577771+00:00
-- url     : https://prove2.me/theorems/cd11bb62-0994-484e-8f50-85f4eeece471
-- title:
--   Finite Vitali selection of disjoint sets
-- statement:
--   Let $s$ be a finite index set, $B_a$ nonempty sets and $\delta_a\in\mathbb R$ sizes for $a\in s$. Then there is a subfamily $u\subseteq s$ of pairwise disjoint sets such that every $B_a$ meets some selected set at least as large:
--   $$
--   \forall a\in s\ \exists b\in u:\quad B_a\cap B_b\ne\emptyset\ \text{and}\ \delta_a\le\delta_b .
--   $$
--
--   This is the combinatorial core of the Vitali covering lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/FiniteVitali.lean#L11-L48

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

open OAI OAI.TriangularHilbert
universe uκ uX
open scoped BigOperators

theorem OAI.TriangularHilbert.finite_disjoint_selection {κ : Type uκ} {X : Type uX} (s : Finset κ) (B : κ → Set X)
  (δ : κ → ℝ) (hne : ∀ a ∈ s, (B a).Nonempty) :
  ∃ u : Finset κ, u ⊆ s ∧
    (∀ a ∈ u, ∀ b ∈ u, a ≠ b → Disjoint (B a) (B b)) ∧
    ∀ a ∈ s, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ δ a ≤ δ b := by sorry

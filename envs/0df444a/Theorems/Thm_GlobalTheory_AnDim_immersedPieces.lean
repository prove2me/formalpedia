-- Prove2me | Theorems.Thm_GlobalTheory_AnDim_immersedPieces
-- name    : GlobalTheory.AnDim.immersedPieces
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:35.255935+00:00
-- url     : https://prove2.me/theorems/354f0175-f31d-4c3e-ab96-47c409d13fd6
-- title:
--   An Dim: immersed Pieces
-- statement:
--   The An Dim construction uses the immersed Pieces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L192-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L192-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.AnDim.immersedPieces (h : Published.AnalyticSetDimension) (d : ℕ) (X : Type) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (A : FinHolAtlas d X) :
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      ¬ HasHoloImm A Z (n + 1)) ∧
    (∀ (C S : Set X) (k : ℕ), IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      HasHoloImm A (C ∩ S) k → HasHoloImm A C (k + 1)) ∧
    (∀ S : Set X, A.IsAnalyticSubset S →
      {C | IsIrreducibleComponent A S C}.Finite ∧ S = ⋃₀ {C | IsIrreducibleComponent A S C}) := by sorry

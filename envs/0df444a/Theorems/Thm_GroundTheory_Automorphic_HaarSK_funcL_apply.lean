-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HaarSK_funcL_apply
-- name    : GroundTheory.Automorphic.HaarSK.funcL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:07.86461+00:00
-- url     : https://prove2.me/theorems/cef283da-5eed-46fa-9006-656cad954788
-- title:
--   Haar SK: func L apply
-- statement:
--   The Haar SK construction uses the func L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L196-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L196-L197

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.HaarSK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {S K : Subgroup G}
variable (hSK : Surjective (mulMap S K))
variable {hSK}
variable [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
variable {mL : Measure (inter S K)}
variable [LocallyCompactSpace S] [CompactSpace (inter S K)]
variable (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
include hS hK
variable (mL) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure mL]
  [mL.IsMulLeftInvariant]

theorem GroundTheory.Automorphic.HaarSK.funcL_apply (v : CompactlySupportedContinuousMap S ℝ) :
    funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v = ∫ g, lift hSK (flat mL v) g ∂μ := by sorry

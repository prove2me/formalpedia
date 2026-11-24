-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HaarSK_translate_apply
-- name    : GroundTheory.Automorphic.HaarSK.translate_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:16.445057+00:00
-- url     : https://prove2.me/theorems/205e4e28-2ab8-4049-bcc0-1fc185a09534
-- title:
--   Haar SK: translate apply
-- statement:
--   The Haar SK construction uses the translate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L212-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L212-L213

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

theorem GroundTheory.Automorphic.HaarSK.translate_apply (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) (s : S) :
    translate s₀ v s = v (s₀ * s) := by sorry

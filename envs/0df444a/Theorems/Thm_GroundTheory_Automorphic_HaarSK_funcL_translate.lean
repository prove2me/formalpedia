-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HaarSK_funcL_translate
-- name    : GroundTheory.Automorphic.HaarSK.funcL_translate
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:00.956853+00:00
-- url     : https://prove2.me/theorems/c58943e2-3bba-4408-8242-d8df0c117a38
-- title:
--   Haar SK: func L translate
-- statement:
--   The Haar SK construction uses the func L translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L229-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L229-L234

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
variable {mL : Measure (inter S K)} [LocallyCompactSpace S] [CompactSpace (inter S K)]
  [IsFiniteMeasure mL] [mL.IsMulLeftInvariant]
  {hS : IsClosed (S : Set G)} {hK : IsCompact (K : Set G)} {hSK : Surjective (mulMap S K)}
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

theorem GroundTheory.Automorphic.HaarSK.funcL_translate (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) :
    funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) (translate s₀ v) =
      funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v := by sorry

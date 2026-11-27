-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HaarSK_lift_mul
-- name    : GroundTheory.Automorphic.HaarSK.lift_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:02.298081+00:00
-- url     : https://prove2.me/theorems/d900a1bd-56ce-5ab2-bade-f2b4c5ab3b65
-- title:
--   Haar SK: lift mul
-- statement:
--   The Haar SK construction uses the lift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L80-L82

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

theorem GroundTheory.Automorphic.HaarSK.lift_mul {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) (s : S) (k : K) :
    lift hSK u ((s : G) * k) = u s := by sorry

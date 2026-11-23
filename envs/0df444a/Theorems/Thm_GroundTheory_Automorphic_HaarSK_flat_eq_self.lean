-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HaarSK_flat_eq_self
-- name    : GroundTheory.Automorphic.HaarSK.flat_eq_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:47.568526+00:00
-- url     : https://prove2.me/theorems/c49d0658-4007-4673-af01-96eb100ba3b4
-- title:
--   Haar SK: flat eq self
-- statement:
--   The Haar SK construction uses the flat eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L107-L112

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

theorem GroundTheory.Automorphic.HaarSK.flat_eq_self [IsProbabilityMeasure mL] {u : S → ℝ}
    (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) : flat mL u = u := by sorry

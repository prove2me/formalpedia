-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HaarSK_integral_rmk
-- name    : GroundTheory.Automorphic.HaarSK.integral_rmk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:03.07599+00:00
-- url     : https://prove2.me/theorems/a12e868e-a1f6-4f27-b4f1-9fbf18ebd9da
-- title:
--   Haar SK: integral rmk
-- statement:
--   The Haar SK construction uses the integral rmk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L240-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean#L240-L242

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
variable (mL hS hK hSK μ)

theorem GroundTheory.Automorphic.HaarSK.integral_rmk (v : CompactlySupportedContinuousMap S ℝ) :
    ∫ s, v s ∂rmk mL hS hK hSK μ = funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v := by sorry

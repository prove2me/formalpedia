-- Prove2me | Theorems.Thm_GlobalTheory_VolPairExists_exists_haar_image
-- name    : GlobalTheory.VolPairExists.exists_haar_image
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:57.472235+00:00
-- url     : https://prove2.me/theorems/c8a5ba42-7d5c-502b-824a-8baeffb48231
-- title:
--   Vol Pair Exists: exists haar image
-- statement:
--   The Vol Pair Exists construction uses the exists haar image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L12-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LeftInvOfUnitary.lean#L12-L69

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.VolPairExists

theorem GlobalTheory.VolPairExists.exists_haar_image {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Continuous ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t)
    (hf : ∀ t, ∃ W ∈ 𝓝 t, ∃ K : Set G, IsCompact K ∧ (H : Set G) ∩ ψ ⁻¹' W ⊆ K) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ s, MeasurableSet s → μ (ψ ⁻¹' s ∩ H) = ν s := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_NAK_exists_eq_smul_map_mulMap_of_right
-- name    : GlobalTheory.NAK.exists_eq_smul_map_mulMap_of_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:42:46.662802+00:00
-- url     : https://prove2.me/theorems/98e2ca5b-fd08-42ce-8dc5-2defb5f88245
-- title:
--   NAK: exists eq smul map mul Map of right
-- statement:
--   The NAK construction uses the exists eq smul map mul Map of right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureIwasawaQuotient.lean#L39-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureIwasawaQuotient.lean#L39-L142

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectHaar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureIwasawaQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace GroundTheory.Automorphic.HaarSK
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.NAK

theorem GlobalTheory.NAK.exists_eq_smul_map_mulMap_of_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (S K : Subgroup G)
    (μ : Measure G) [μ.IsHaarMeasure] (hright : ∀ k ∈ K, μ.map (· * k) = μ)
    (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
    (μS : Measure S) [μS.IsHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, μ = c • map (mulMap S K) (μS.prod μK) := by sorry

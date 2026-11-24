-- Prove2me | Theorems.Thm_GlobalTheory_LabelsAgree_eq_one_of_sums
-- name    : GlobalTheory.LabelsAgree.eq_one_of_sums
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:33.6018+00:00
-- url     : https://prove2.me/theorems/9961d0cd-bfff-4a54-bac5-663fc72c58fd
-- title:
--   Labels Agree: eq one of sums
-- statement:
--   The Labels Agree construction uses the eq one of sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLabelsAgreeOfIso.lean#L252-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLabelsAgreeOfIso.lean#L252-L277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.LabelsAgree

theorem GlobalTheory.LabelsAgree.eq_one_of_sums {C X : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} (hm : ‖(m : C)‖ = 1)
    (T : X → C) (hT : Filter.Tendsto T Filter.cofinite (nhds 0)) (h0 : T 0 ≠ 0)
    (hdom : ∀ z, z ≠ 0 → ‖T (m • z)‖ < ‖T 0‖) (w : C) (τ : Multiplicative X →* Cˣ) (hτ : τ ^ m = 1)
    (h : ∀ u : Multiplicative X →* Cˣ, u ^ m = 1 →
      ∑' χ, w * (τ (Multiplicative.ofAdd χ) : C) * T χ * (u (Multiplicative.ofAdd χ) : C) =
        ∑' χ, T χ * (u (Multiplicative.ofAdd χ) : C)) : w = 1 := by sorry

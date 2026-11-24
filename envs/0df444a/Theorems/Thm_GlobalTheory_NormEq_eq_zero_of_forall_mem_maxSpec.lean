-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_eq_zero_of_forall_mem_maxSpec
-- name    : GlobalTheory.NormEq.eq_zero_of_forall_mem_maxSpec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:39.486801+00:00
-- url     : https://prove2.me/theorems/b46b2073-61dd-40c0-8939-eb48dd9e04bc
-- title:
--   Norm Eq: eq zero of forall mem max Spec
-- statement:
--   The Norm Eq construction uses the eq zero of forall mem max Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormApproximationFirstLevel.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormApproximationFirstLevel.lean#L12-L18

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq

theorem GlobalTheory.NormEq.eq_zero_of_forall_mem_maxSpec {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A] {y : A}
    (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by sorry

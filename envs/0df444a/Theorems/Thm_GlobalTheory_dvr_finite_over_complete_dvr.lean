-- Prove2me | Theorems.Thm_GlobalTheory_dvr_finite_over_complete_dvr
-- name    : GlobalTheory.dvr_finite_over_complete_dvr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:44.662455+00:00
-- url     : https://prove2.me/theorems/c6499c73-18ec-4f0c-bcf9-22796c4204f9
-- title:
--   Global Theory: dvr finite over complete dvr
-- statement:
--   The Global Theory construction uses the dvr finite over complete dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/InjectiveAlgebraMapOfDvrOfIsIntegral.lean#L10-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/InjectiveAlgebraMapOfDvrOfIsIntegral.lean#L10-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_InjectiveAlgebraMapOfDvrOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
open IsLocalRing

theorem GlobalTheory.dvr_finite_over_complete_dvr :
    ∀ (O V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing V] [IsDomain V]
      [IsDiscreteValuationRing V] [Algebra O V] [Module.Finite O V],
      Function.Injective (algebraMap O V) ∧ IsLocalHom (algebraMap O V) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V ∧
          (Finite (IsLocalRing.ResidueField O) → Finite (IsLocalRing.ResidueField V)) := by sorry

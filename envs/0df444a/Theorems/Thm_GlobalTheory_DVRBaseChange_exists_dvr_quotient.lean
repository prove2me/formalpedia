-- Prove2me | Theorems.Thm_GlobalTheory_DVRBaseChange_exists_dvr_quotient
-- name    : GlobalTheory.DVRBaseChange.exists_dvr_quotient
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:35:18.152831+00:00
-- url     : https://prove2.me/theorems/182afab5-f7ea-4b96-9705-0c12c63f0806
-- title:
--   DVRBase Change: exists dvr quotient
-- statement:
--   The DVRBase Change construction uses the exists dvr quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsUnramifiedExtension.lean#L8-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsUnramifiedExtension.lean#L8-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsUnramifiedExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DVRBaseChange

theorem GlobalTheory.DVRBaseChange.exists_dvr_quotient (W : Type) [CommRing W] [IsLocalRing W] (π : W)
    (hm : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ : ¬ IsNilpotent π) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : W →+* V), Irreducible (q π) := by sorry

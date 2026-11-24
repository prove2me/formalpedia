-- Prove2me | Theorems.Thm_GlobalTheory_DVRBaseChange_exists_dvr_of_isRadical
-- name    : GlobalTheory.DVRBaseChange.exists_dvr_of_isRadical
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:04.095308+00:00
-- url     : https://prove2.me/theorems/52ab4f65-db62-4681-804d-b4d6ecedfeef
-- title:
--   DVRBase Change: exists dvr of is Radical
-- statement:
--   The DVRBase Change construction uses the exists dvr of is Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsUnramifiedExtension.lean#L71-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsUnramifiedExtension.lean#L71-L95

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

theorem GlobalTheory.DVRBaseChange.exists_dvr_of_isRadical (S : Type) [CommRing S] (π : S)
    (hrad : (Ideal.span {π}).IsRadical) (hne : Ideal.span {π} ≠ ⊤)
    (hreg : ∀ s, π * s = 0 → s = 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : S →+* V), Irreducible (q π) := by sorry

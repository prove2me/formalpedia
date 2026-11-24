-- Prove2me | Theorems.Thm_GlobalTheory_residue_localization_surjective_of_isMaximal
-- name    : GlobalTheory.residue_localization_surjective_of_isMaximal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:04.766933+00:00
-- url     : https://prove2.me/theorems/30923b0a-ad6a-48a6-9216-fb6a28875246
-- title:
--   Global Theory: residue localization surjective of is Maximal
-- statement:
--   The Global Theory construction uses the residue localization surjective of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationResidueFiniteUnram.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationResidueFiniteUnram.lean#L6-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.residue_localization_surjective_of_isMaximal {S : Type} [CommRing S] (q : Ideal S) [q.IsMaximal] :
    Function.Surjective ((IsLocalRing.residue (Localization.AtPrime q)).comp (algebraMap S (Localization.AtPrime q))) := by sorry

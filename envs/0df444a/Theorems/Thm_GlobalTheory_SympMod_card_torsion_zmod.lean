-- Prove2me | Theorems.Thm_GlobalTheory_SympMod_card_torsion_zmod
-- name    : GlobalTheory.SympMod.card_torsion_zmod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:25:59.609559+00:00
-- url     : https://prove2.me/theorems/9865fc51-b01c-453b-9ead-9a4b579af14b
-- title:
--   Symp Mod: card torsion zmod
-- statement:
--   The Symp Mod construction uses the card torsion zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L10-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SympMod

theorem GlobalTheory.SympMod.card_torsion_zmod {M d : ℕ} [NeZero M] (hd : d ∣ M) :
    Nat.card {a : ZMod M // d • a = 0} = d := by sorry

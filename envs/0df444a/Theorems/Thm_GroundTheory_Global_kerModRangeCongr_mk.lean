-- Prove2me | Theorems.Thm_GroundTheory_Global_kerModRangeCongr_mk
-- name    : GroundTheory.Global.kerModRangeCongr_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:25.936122+00:00
-- url     : https://prove2.me/theorems/790171d8-9624-4f68-bd16-c9dd1aeb425e
-- title:
--   Global: ker Mod Range Congr mk
-- statement:
--   The Global construction uses the ker Mod Range Congr mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L45-L49

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem GroundTheory.Global.kerModRangeCongr_mk {fA gA : A →+ A} {fB gB : B →+ B} (e : A ≃+ B)
    (hf : ∀ a, e (fA a) = fB (e a)) (hg : ∀ a, e (gA a) = gB (e a)) (a : fA.ker) :
    kerModRangeCongr e hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      QuotientAddGroup.mk (kerMap e.toAddMonoidHom hf a) := by sorry

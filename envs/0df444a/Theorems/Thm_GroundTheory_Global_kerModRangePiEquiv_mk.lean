-- Prove2me | Theorems.Thm_GroundTheory_Global_kerModRangePiEquiv_mk
-- name    : GroundTheory.Global.kerModRangePiEquiv_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:12.94032+00:00
-- url     : https://prove2.me/theorems/a697ba8c-cfa1-542b-b9eb-6932d27a2348
-- title:
--   Global: ker Mod Range Pi Equiv mk
-- statement:
--   The Global construction uses the ker Mod Range Pi Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L85-L91

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

theorem GroundTheory.Global.kerModRangePiEquiv_mk {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
    (F G : (∀ i, A i) →+ (∀ i, A i)) (f g : ∀ i, A i →+ A i) (hF : ∀ x i, F x i = f i (x i))
    (hG : ∀ x i, G x i = g i (x i)) (x : F.ker) (i : ι) :
    kerModRangePiEquiv F G f g hF hG (QuotientAddGroup.mk x : KerModRange F G) i =
      QuotientAddGroup.mk (⟨(x : ∀ i, A i) i, by
        rw [AddMonoidHom.mem_ker, ← hF, AddMonoidHom.mem_ker.1 x.2, Pi.zero_apply]⟩ : (f i).ker) := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AdicCompletion_mk_extendRingHom
-- name    : GroundTheory.PAdicHodge.AdicCompletion.mk_extendRingHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:01:35.744813+00:00
-- url     : https://prove2.me/theorems/24957e20-5b39-5af9-a3a0-a89e1ab6cfd6
-- title:
--   Adic Completion: mk extend Ring Hom
-- statement:
--   The Adic Completion construction uses the mk extend Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L73-L78

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
variable {A B : Type*} [CommRing A] [CommRing B]

theorem GroundTheory.PAdicHodge.AdicCompletion.mk_extendRingHom (J : Ideal A) (I : Ideal B) [IsAdicComplete I B]
    (f : A →+* B) (hf : J ≤ I.comap f) (n : ℕ) (x : AdicCompletion J A) :
    Ideal.Quotient.mk (I ^ n) (AdicCompletion.extendRingHom J I f hf x) =
      Ideal.quotientMap (I ^ n) f ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n))
        (AdicCompletion.evalₐ J n x) := by sorry

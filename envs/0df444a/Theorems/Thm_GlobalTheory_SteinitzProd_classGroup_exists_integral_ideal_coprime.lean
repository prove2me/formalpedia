-- Prove2me | Theorems.Thm_GlobalTheory_SteinitzProd_classGroup_exists_integral_ideal_coprime
-- name    : GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:57.833253+00:00
-- url     : https://prove2.me/theorems/40783405-b4a5-4891-a412-e5500bd8e24e
-- title:
--   Steinitz Prod: class Group exists integral ideal coprime
-- statement:
--   The Steinitz Prod construction uses the class Group exists integral ideal coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SteinitzPiIdealsLinearEquivOfClassGroupProd.lean#L31-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SteinitzPiIdealsLinearEquivOfClassGroupProd.lean#L31-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SteinitzProd
variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime {m : Ideal R} (hm : m ≠ ⊥) (c : ClassGroup R) :
    ∃ I : (Ideal R)⁰, (I : Ideal R) ⊔ m = ⊤ ∧ ClassGroup.mk0 I = c := by sorry

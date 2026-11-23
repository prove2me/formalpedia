-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_square
-- name    : GlobalTheory.LocalFlat.relationsLift_of_square
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:43.221806+00:00
-- url     : https://prove2.me/theorems/6b708717-ee4a-4de2-9587-89cd0771c286
-- title:
--   Local Flat: relations Lift of square
-- statement:
--   The Local Flat construction uses the relations Lift of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L158-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L158-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open GlobalTheory.LocalFlat
variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]

theorem GlobalTheory.LocalFlat.relationsLift_of_square {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] {I : Ideal A} (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q) (hpI : RingHom.ker p = I)
    (hqI : RingHom.ker q = I.map (algebraMap A B)) (hsq : ψ.comp p = q.comp (algebraMap A B))
    (hψ : ψ.Flat) : RelationsLift I B := by sorry

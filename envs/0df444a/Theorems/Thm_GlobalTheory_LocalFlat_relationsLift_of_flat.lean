-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_flat
-- name    : GlobalTheory.LocalFlat.relationsLift_of_flat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:59.518802+00:00
-- url     : https://prove2.me/theorems/6b5e90d4-1bd2-420f-85ab-6b367b5f03d5
-- title:
--   Local Flat: relations Lift of flat
-- statement:
--   The Local Flat construction uses the relations Lift of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L30-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L30-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
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

theorem GlobalTheory.LocalFlat.relationsLift_of_flat {I : Ideal A} {C : Type*} [CommRing C] [Algebra A C]
    (hC : Function.Surjective (algebraMap A C)) (hI : RingHom.ker (algebraMap A C) = I)
    {M' : Type*} [AddCommGroup M'] [Module A M'] [Module C M'] [IsScalarTower A C M']
    [Module.Flat C M'] (q : M →ₗ[A] M') (hq : Function.Surjective q)
    (hker : ker q = I • (⊤ : Submodule A M)) : RelationsLift I M := by sorry

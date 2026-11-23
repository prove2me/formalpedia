-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlat_flat_of_relationsLift
-- name    : GlobalTheory.LocalFlat.flat_of_relationsLift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:45.73047+00:00
-- url     : https://prove2.me/theorems/3a074b8d-4a90-4f56-8435-fad3c7858099
-- title:
--   Local Flat: flat of relations Lift
-- statement:
--   The Local Flat construction uses the flat of relations Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L116-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L116-L156

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

theorem GlobalTheory.LocalFlat.flat_of_relationsLift [IsNoetherianRing A] (B : Type v) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (h : ∀ n, RelationsLift (I ^ n) M) :
    Module.Flat A M := by sorry

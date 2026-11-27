-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_isSMulRegular_of_flat_quotient
-- name    : GlobalTheory.flat_of_isSMulRegular_of_flat_quotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:04.627812+00:00
-- url     : https://prove2.me/theorems/bb9bb09e-1cb2-4f35-86d7-3769522c87c7
-- title:
--   Global Theory: flat of is SMul Regular of flat quotient
-- statement:
--   The Global Theory construction uses the flat of is SMul Regular of flat quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L190-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L190-L200

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
open IsLocalRing

theorem GlobalTheory.flat_of_isSMulRegular_of_flat_quotient {A : Type u} (B : Type v) {M : Type w} [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [AddCommGroup M]
    [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {π : A}
    (hπ : algebraMap A B π ∈ Ideal.jacobson (⊥ : Ideal B)) (hreg : IsSMulRegular M π)
    [Module.Flat (A ⧸ Ideal.span {π}) (M ⧸ (Ideal.span {π} • ⊤ : Submodule A M))] :
    Module.Flat A M := by sorry

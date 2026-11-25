-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_flat_quotient_pow
-- name    : GlobalTheory.flat_of_flat_quotient_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:55.086535+00:00
-- url     : https://prove2.me/theorems/7b947d32-8c7a-5886-be32-1a8770a7b045
-- title:
--   Global Theory: flat of flat quotient pow
-- statement:
--   The Global Theory construction uses the flat of flat quotient pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L179-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L179-L188

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

theorem GlobalTheory.flat_of_flat_quotient_pow {A : Type u} (B : Type v) {M : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule A M))) :
    Module.Flat A M := by sorry

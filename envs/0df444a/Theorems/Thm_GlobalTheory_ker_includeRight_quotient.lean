-- Prove2me | Theorems.Thm_GlobalTheory_ker_includeRight_quotient
-- name    : GlobalTheory.ker_includeRight_quotient
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:29.813131+00:00
-- url     : https://prove2.me/theorems/093915e7-7deb-4cb4-8c7a-5a256d700064
-- title:
--   Global Theory: ker include Right quotient
-- statement:
--   The Global Theory construction uses the ker include Right quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L262-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L262-L270

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
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra T A] [Algebra T B] [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B]

theorem GlobalTheory.ker_includeRight_quotient {T : Type*} (A : Type*) [CommRing T] [CommRing A] [Algebra T A]
    (I : Ideal T) :
    RingHom.ker ((Algebra.TensorProduct.includeRight : A →ₐ[T] (T ⧸ I) ⊗[T] A) :
      A →+* (T ⧸ I) ⊗[T] A) = I.map (algebraMap T A) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_flat_quotientMap_dvr
-- name    : GlobalTheory.flat_of_flat_quotientMap_dvr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:49.086819+00:00
-- url     : https://prove2.me/theorems/fe1b39b1-306b-54dc-96c6-ff8aa5f2ce53
-- title:
--   Global Theory: flat of flat quotient Map dvr
-- statement:
--   The Global Theory construction uses the flat of flat quotient Map dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L254-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L254-L260

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

theorem GlobalTheory.flat_of_flat_quotientMap_dvr (φ : A →ₐ[T] B)
    (hle : (maximalIdeal T).map (algebraMap T A) ≤
      ((maximalIdeal T).map (algebraMap T B)).comap (φ : A →+* B))
    (h : (Ideal.quotientMap _ (φ : A →+* B) hle).Flat) : (φ : A →+* B).Flat := by sorry

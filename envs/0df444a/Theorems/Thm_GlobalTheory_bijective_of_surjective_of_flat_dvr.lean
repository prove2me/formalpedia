-- Prove2me | Theorems.Thm_GlobalTheory_bijective_of_surjective_of_flat_dvr
-- name    : GlobalTheory.bijective_of_surjective_of_flat_dvr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:27.905388+00:00
-- url     : https://prove2.me/theorems/1899bc1d-c6b0-459a-9e3a-480c6758bafa
-- title:
--   Global Theory: bijective of surjective of flat dvr
-- statement:
--   The Global Theory construction uses the bijective of surjective of flat dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L527-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L527-L534

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

theorem GlobalTheory.bijective_of_surjective_of_flat_dvr {T R S : Type*} [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra T R] [IsLocalHom (algebraMap T R)] [CommRing S] [Nontrivial S] [Algebra T S]
    [Module.Flat T S] (q : R →ₐ[T] S) (hq : Function.Surjective q) : Function.Bijective q := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_flat_reduction_dvr
-- name    : GlobalTheory.flat_of_flat_reduction_dvr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:06.074311+00:00
-- url     : https://prove2.me/theorems/3288e0e3-7c71-4709-ba0d-f3b870e1d34d
-- title:
--   Global Theory: flat of flat reduction dvr
-- statement:
--   The Global Theory construction uses the flat of flat reduction dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L232-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L232-L252

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
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra T A] [Algebra T B] [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B]

theorem GlobalTheory.flat_of_flat_reduction_dvr {C D : Type*} [CommRing C] [CommRing D] (φ : A →ₐ[T] B)
    (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hp𝔪 : RingHom.ker p = (maximalIdeal T).map (algebraMap T A))
    (hq𝔪 : RingHom.ker q = (maximalIdeal T).map (algebraMap T B))
    (hsq : ψ.comp p = q.comp φ) (hψ : ψ.Flat) : (φ : A →+* B).Flat := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_injective_and_isLocalHom_adicCompletion_comp
-- name    : GlobalTheory.injective_and_isLocalHom_adicCompletion_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:12.034449+00:00
-- url     : https://prove2.me/theorems/d5d198fb-0b9d-42aa-b6c7-85f7aed73261
-- title:
--   Global Theory: injective and is Local Hom adic Completion comp
-- statement:
--   The Global Theory construction uses the injective and is Local Hom adic Completion comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L598-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L598-L603

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem GlobalTheory.injective_and_isLocalHom_adicCompletion_comp {S : Type*} [CommRing S] {V : Type*}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : S →+* V)
    (hf : Function.Injective f) [IsLocalHom f] :
    Function.Injective ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp f) ∧
      IsLocalHom ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp f) := by sorry

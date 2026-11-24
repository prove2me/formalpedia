-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobian_map_mem_radical
-- name    : GlobalTheory.DiscrJacobian.map_mem_radical
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:13.036934+00:00
-- url     : https://prove2.me/theorems/d5fa8665-a84d-4de0-99c9-1d725bc61a3d
-- title:
--   Discr Jacobian: map mem radical
-- statement:
--   The Discr Jacobian construction uses the map mem radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L286-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean#L286-L305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
open MvPowerSeries IsLocalRing
open MvPowerSeries IsLocalRing
open scoped TensorProduct

theorem GlobalTheory.DiscrJacobian.map_mem_radical {R S B : Type} [CommRing R]
    [IsLocalRing R] [CommRing S] [CommRing B]
    [Algebra R B] [Algebra S B] [Module.Finite R B] (hsurj : Function.Surjective (algebraMap S B))
    {x : S} (hx : x ∈ (⊥ : Ideal S).jacobson) :
    algebraMap S B x ∈ ((maximalIdeal R).map (algebraMap R B)).radical := by sorry

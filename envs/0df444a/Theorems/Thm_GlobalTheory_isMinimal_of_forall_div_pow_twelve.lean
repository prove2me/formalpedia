-- Prove2me | Theorems.Thm_GlobalTheory_isMinimal_of_forall_div_pow_twelve
-- name    : GlobalTheory.isMinimal_of_forall_div_pow_twelve
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:57.182153+00:00
-- url     : https://prove2.me/theorems/ec832e80-2a0a-4408-8392-e13aa416fbb9
-- title:
--   Global Theory: is Minimal of forall div pow twelve
-- statement:
--   The Global Theory construction uses the is Minimal of forall div pow twelve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMinimalOfForallDivPowTwelve.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMinimalOfForallDivPowTwelve.lean#L7-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMinimalOfForallDivPowTwelve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain WeierstrassCurve
open GlobalTheory

theorem GlobalTheory.isMinimal_of_forall_div_pow_twelve (R F : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (W : WeierstrassCurve F) (hI : W.IsIntegral R)
    (h : ∀ x : R, x ≠ 0 → W.Δ / algebraMap R F x ^ 12 ∈ (algebraMap R F).range → IsUnit x) :
    W.IsMinimal R := by sorry

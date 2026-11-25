-- Prove2me | Theorems.Thm_GlobalTheory_CoordsAlg_cotFun_toCotangent
-- name    : GlobalTheory.CoordsAlg.cotFun_toCotangent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:42.384572+00:00
-- url     : https://prove2.me/theorems/463ee3b4-8356-49f6-8ed2-11f4b1177450
-- title:
--   Coords Alg: cot Fun to Cotangent
-- statement:
--   The Coords Alg construction uses the cot Fun to Cotangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivationFamilyCotangentBasis.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivationFamilyCotangentBasis.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationFamilyCotangentBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoordsAlg

theorem GlobalTheory.CoordsAlg.cotFun_toCotangent {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) (x : I) :
    cotFun I f hf (I.toCotangent x) = f x := by sorry

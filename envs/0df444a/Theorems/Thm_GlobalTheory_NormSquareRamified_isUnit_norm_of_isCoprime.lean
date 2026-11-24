-- Prove2me | Theorems.Thm_GlobalTheory_NormSquareRamified_isUnit_norm_of_isCoprime
-- name    : GlobalTheory.NormSquareRamified.isUnit_norm_of_isCoprime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:00.634689+00:00
-- url     : https://prove2.me/theorems/37bbe973-2465-4aee-941e-12f2413ebb72
-- title:
--   Norm Square Ramified: is Unit norm of is Coprime
-- statement:
--   The Norm Square Ramified construction uses the is Unit norm of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitNormOfIsCoprime.lean#L35-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitNormOfIsCoprime.lean#L35-L52

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitNormOfIsCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormSquareRamified

theorem GlobalTheory.NormSquareRamified.isUnit_norm_of_isCoprime {F : Type*} [Field F] [NumberField F] (n : ℕ) (y : 𝓞 F)
    (h : IsCoprime y (n : 𝓞 F)) : IsUnit ((Algebra.norm ℤ y : ℤ) : ZMod n) := by sorry

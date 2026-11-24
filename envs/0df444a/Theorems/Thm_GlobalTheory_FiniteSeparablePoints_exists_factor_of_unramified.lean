-- Prove2me | Theorems.Thm_GlobalTheory_FiniteSeparablePoints_exists_factor_of_unramified
-- name    : GlobalTheory.FiniteSeparablePoints.exists_factor_of_unramified
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:24.311538+00:00
-- url     : https://prove2.me/theorems/baf31ebe-4289-4b84-be33-060cc62784aa
-- title:
--   Finite Separable Points: exists factor of unramified
-- statement:
--   The Finite Separable Points construction uses the exists factor of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFiniteSeparablePoint.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFiniteSeparablePoint.lean#L7-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteSeparablePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FiniteSeparablePoints

theorem GlobalTheory.FiniteSeparablePoints.exists_factor_of_unramified {k Ω S : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing S]
    [Algebra k S] [Algebra.FormallyUnramified k S] [Algebra.FiniteType k S] (φ : S →ₐ[k] Ω) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ ψ : S →+* K, (algebraMap K Ω).comp ψ = φ.toRingHom := by sorry

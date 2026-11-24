-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_lift_of_henselian
-- name    : GlobalTheory.exists_algHom_lift_of_henselian
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:16.900747+00:00
-- url     : https://prove2.me/theorems/44ee63b9-ca66-4d72-9a04-2a12c7123193
-- title:
--   Global Theory: exists alg Hom lift of henselian
-- statement:
--   The Global Theory construction uses the exists alg Hom lift of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L256-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L256-L283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
open Polynomial

theorem GlobalTheory.exists_algHom_lift_of_henselian {B A : Type*} {R K : Type u} [CommRing B] [CommRing A]
    [CommRing R] [Field K] [Algebra B A] [Algebra B R] [Algebra B K] [Algebra.Etale B A]
    [HenselianLocalRing R] (π : R →ₐ[B] K) (hπ : Function.Surjective π) (φ : A →ₐ[B] K) :
    ∃ ψ : A →ₐ[B] R, π.comp ψ = φ := by sorry

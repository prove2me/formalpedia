-- Prove2me | Theorems.Thm_GlobalTheory_kaehler_fibre_equiv_pushout_formallyEtale
-- name    : GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:30.543157+00:00
-- url     : https://prove2.me/theorems/14d09590-acad-4fe9-8963-96398a00483f
-- title:
--   Global Theory: kaehler fibre equiv pushout formally Etale
-- statement:
--   The Global Theory construction uses the kaehler fibre equiv pushout formally Etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KaehlerFibreEquivPushoutFormallyEtale.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KaehlerFibreEquivPushoutFormallyEtale.lean#L9-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KaehlerFibreEquivPushoutFormallyEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open KaehlerDifferential TensorProduct

theorem GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale :
    ∀ (R R' B C B' K : Type) [CommRing R] [CommRing R'] [CommRing B] [CommRing C] [CommRing B'] [Field K] [Algebra R R'] [Algebra R B] [Algebra R C] [Algebra R' C] [Algebra B C] [IsScalarTower R R' C] [IsScalarTower R B C] [Algebra.IsPushout R R' B C] [Algebra C B'] [Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [Algebra B' K] [Algebra B K], (∀ x : B, algebraMap B K x = algebraMap B' K (algebraMap C B' (algebraMap B C x))) → ∃ e : (K ⊗[B] Ω[B⁄R]) ≃ₗ[K] (K ⊗[B'] Ω[B'⁄R']), ∀ x : B, e ((1 : K) ⊗ₜ[B] KaehlerDifferential.D R B x) = (1 : K) ⊗ₜ[B'] KaehlerDifferential.D R' B' (algebraMap C B' (algebraMap B C x)) := by sorry

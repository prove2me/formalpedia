-- Prove2me | Theorems.Thm_GlobalTheory_isPushout_of_pi_components_alg
-- name    : GlobalTheory.isPushout_of_pi_components_alg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:57.789269+00:00
-- url     : https://prove2.me/theorems/b9a101f8-b828-439b-b40c-6452223d1337
-- title:
--   Global Theory: is Pushout of pi components alg
-- statement:
--   The Global Theory construction uses the is Pushout of pi components alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RingHomIsPushoutOfPiComponents.lean#L6-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RingHomIsPushoutOfPiComponents.lean#L6-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomIsPushoutOfPiComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.isPushout_of_pi_components_alg {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A']
    [CommRing P'] {n : ℕ} {Q Q' : Fin n → Type} [∀ i, CommRing (Q i)] [∀ i, CommRing (Q' i)]
    [Algebra A P] [Algebra A A'] [Algebra P P'] [Algebra A' P'] [Algebra A P']
    [IsScalarTower A P P'] [IsScalarTower A A' P']
    [∀ i, Algebra A (Q i)] [∀ i, Algebra (Q i) (Q' i)] [∀ i, Algebra A' (Q' i)]
    [∀ i, Algebra A (Q' i)] [∀ i, IsScalarTower A (Q i) (Q' i)] [∀ i, IsScalarTower A A' (Q' i)]
    (g : ∀ i, P →ₐ[A] Q i) (g' : ∀ i, P' →ₐ[A'] Q' i)
    (hg : Function.Bijective (fun (x : P) (i : Fin n) => g i x))
    (hg' : Function.Bijective (fun (x : P') (i : Fin n) => g' i x))
    (hk : ∀ i x, g' i (algebraMap P P' x) = algebraMap (Q i) (Q' i) (g i x))
    (H : ∀ i, Algebra.IsPushout A A' (Q i) (Q' i)) : Algebra.IsPushout A A' P P' := by sorry

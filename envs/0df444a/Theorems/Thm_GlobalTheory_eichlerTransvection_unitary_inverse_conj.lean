-- Prove2me | Theorems.Thm_GlobalTheory_eichlerTransvection_unitary_inverse_conj
-- name    : GlobalTheory.eichlerTransvection_unitary_inverse_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:43.081523+00:00
-- url     : https://prove2.me/theorems/3b94e35a-736d-523a-81a0-ce84aebcf875
-- title:
--   Global Theory: eichler Transvection unitary inverse conj
-- statement:
--   The Global Theory construction uses the eichler Transvection unitary inverse conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EichlerTransvectionUnitaryInverseConj.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EichlerTransvectionUnitaryInverseConj.lean#L7-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EichlerTransvectionUnitaryInverseConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.eichlerTransvection_unitary_inverse_conj :
    ∀ (A : Type) [CommRing A] [StarRing A] [Invertible (2 : A)] (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι A) (_ : Gᴴ = G) (h : (ι → A) → (ι → A) → A) (_ : ∀ x y, h x y = star y ⬝ᵥ G.mulVec x) (E : (ι → A) → (ι → A) → (ι → A) → (ι → A)) (_ : ∀ w v y, E w v y = y + h y v • w - h y w • v - (⅟(2 : A) * h v v * h y w) • w), (∀ w v, h w w = 0 → h w v = 0 → ∀ x y, h (E w v x) (E w v y) = h x y) ∧ (∀ w v, h w w = 0 → h w v = 0 → ∀ y, E w (-v) (E w v y) = y) ∧ ∀ (g : Matrix ι ι A), (∀ x y, h (g.mulVec x) (g.mulVec y) = h x y) → ∀ w v y, g.mulVec (E w v y) = E (g.mulVec w) (g.mulVec v) (g.mulVec y) := by sorry

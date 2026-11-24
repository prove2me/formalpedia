-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_normal_adjoin_algebraic
-- name    : GlobalTheory.exists_finite_normal_adjoin_algebraic
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:34.685348+00:00
-- url     : https://prove2.me/theorems/4640d439-4c94-4981-80fc-f557898cbb30
-- title:
--   Global Theory: exists finite normal adjoin algebraic
-- statement:
--   The Global Theory construction uses the exists finite normal adjoin algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteNormalAdjoinAlgebraic.lean#L16-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteNormalAdjoinAlgebraic.lean#L16-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteNormalAdjoinAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_finite_normal_adjoin_algebraic :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
      (s : AlgebraicClosure (FractionRing R)),
      ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂)
        (h' : FractionRing R →+* FractionRing R₂)
        (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)),
        Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧
        (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧
        (∃ s₂, e s₂ = s) ∧
        ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F),
          ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by sorry

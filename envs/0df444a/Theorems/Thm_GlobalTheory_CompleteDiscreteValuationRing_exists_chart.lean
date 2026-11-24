-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_chart
-- name    : GlobalTheory.CompleteDiscreteValuationRing.exists_chart
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:25.402794+00:00
-- url     : https://prove2.me/theorems/98e3e0bf-a79e-4ef6-a2aa-689bf4badd66
-- title:
--   Complete Discrete Valuation Ring: exists chart
-- statement:
--   The Complete Discrete Valuation Ring construction uses the exists chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L247-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L247-L353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing

theorem GlobalTheory.CompleteDiscreteValuationRing.exists_chart (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A) (g : R →+* A) (t : A),
      Function.Injective g ∧ t ≠ 0 ∧ ¬ IsUnit t ∧ (∀ r ∈ maximalIdeal R, t ∣ g r) ∧
      ∀ i, Associated (g (a i)) (t ^ k i) := by sorry

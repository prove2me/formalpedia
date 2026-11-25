-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_poly_vanishing_of_fiber
-- name    : GlobalTheory.T.exists_poly_vanishing_of_fiber
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:03.306097+00:00
-- url     : https://prove2.me/theorems/d466a3b7-15c7-4ec8-b4e1-53db62d1d9ae
-- title:
--   T: exists poly vanishing of fiber
-- statement:
--   The T construction uses the exists poly vanishing of fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolyVanishingOfFibreStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolyVanishingOfFibreStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolyVanishingOfFibre
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolyVanishingOfFibreStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_poly_vanishing_of_fiber : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by sorry

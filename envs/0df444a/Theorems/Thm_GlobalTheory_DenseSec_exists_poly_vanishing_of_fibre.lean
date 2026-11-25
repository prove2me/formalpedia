-- Prove2me | Theorems.Thm_GlobalTheory_DenseSec_exists_poly_vanishing_of_fibre
-- name    : GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:44:02.62858+00:00
-- url     : https://prove2.me/theorems/7a2b3eae-f7a6-4f5d-bffd-4bf6d2fd301e
-- title:
--   Dense Sec: exists poly vanishing of fibre
-- statement:
--   The Dense Sec construction uses the exists poly vanishing of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolyVanishingOfFibre.lean#L10-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolyVanishingOfFibre.lean#L10-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleChartLocalizationFiniteTypeFormallyUnramifiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolyVanishingOfFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DenseSec
open TensorProduct

theorem GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by sorry

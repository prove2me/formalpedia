-- Prove2me | Theorems.Thm_GlobalTheory_SkewDense_eq_zero_of_rat_comb
-- name    : GlobalTheory.SkewDense.eq_zero_of_rat_comb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:10.285691+00:00
-- url     : https://prove2.me/theorems/99211952-e95b-44fe-8bc2-15d49fa2b2a6
-- title:
--   Skew Dense: eq zero of rat comb
-- statement:
--   The Skew Dense construction uses the eq zero of rat comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L26-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L26-L46

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.SkewDense

theorem GlobalTheory.SkewDense.eq_zero_of_rat_comb {P G : Type} [Fintype G] (r : G → P → ℂ) (Q : MvPolynomial P ℂ)
    (hrat : ∀ t : G → ℚ, MvPolynomial.eval (fun p => ∑ g, (t g : ℂ) * r g p) Q = 0)
    (hspan : ∀ y : P → ℂ, ∃ z : G → ℂ, y = fun p => ∑ g, z g * r g p) : Q = 0 := by sorry

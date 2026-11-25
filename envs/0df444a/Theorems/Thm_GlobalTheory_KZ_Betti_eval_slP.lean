-- Prove2me | Theorems.Thm_GlobalTheory_KZ_Betti_eval_slP
-- name    : GlobalTheory.KZ.Betti.eval_slP
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:18.962057+00:00
-- url     : https://prove2.me/theorems/39ec8b44-85b2-4f39-bf7e-c3f82522fc4f
-- title:
--   Betti: eval sl P
-- statement:
--   The Betti construction uses the eval sl P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L157-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L157-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti
variable {R : Type} [CommRing R]

theorem GlobalTheory.KZ.Betti.eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_KZ_Betti_polySlash_polySlash
-- name    : GlobalTheory.KZ.Betti.polySlash_polySlash
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:49.791831+00:00
-- url     : https://prove2.me/theorems/6f025d1e-47d7-56d9-a4ea-d882e0bc2c04
-- title:
--   Betti: poly Slash poly Slash
-- statement:
--   The Betti construction uses the poly Slash poly Slash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L138-L146

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

theorem GlobalTheory.KZ.Betti.polySlash_polySlash (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP m' (slP m p) = slP (m * m') p := by sorry

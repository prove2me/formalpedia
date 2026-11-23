-- Prove2me | Theorems.Thm_GlobalTheory_KZ_Betti_mem_potSub
-- name    : GlobalTheory.KZ.Betti.mem_potSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:04.726778+00:00
-- url     : https://prove2.me/theorems/15fcb03e-e92c-405a-921c-f9b05b51d82e
-- title:
--   Betti: mem pot Sub
-- statement:
--   The Betti construction uses the mem pot Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L210-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L210-L210

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
variable {w : ℕ} {Γ : Subgroup SL(2, ℤ)}

theorem GlobalTheory.KZ.Betti.mem_potSub {F : ℂ → MvPolynomial (Fin 2) R} : F ∈ potSub R w Γ ↔ F ∈ Pot R w Γ := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_main
-- name    : GlobalTheory.WpFam.AddCharZMod.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:16.539014+00:00
-- url     : https://prove2.me/theorems/9c0aa266-d6ef-40a9-8e7d-af9c80a65b80
-- title:
--   Add Char ZMod: main
-- statement:
--   The Add Char ZMod construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootOfUnityExpZModAdditiveCharacterProperties.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootOfUnityExpZModAdditiveCharacterProperties.lean#L13-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootOfUnityExpZModAdditiveCharacterProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.AddCharZMod

theorem GlobalTheory.WpFam.AddCharZMod.main : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by sorry

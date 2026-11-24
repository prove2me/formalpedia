-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_Act_rightActions
-- name    : GlobalTheory.WpFam.Act.rightActions
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:29.31071+00:00
-- url     : https://prove2.me/theorems/5bcc3b42-4c13-43f3-91c6-f0acfddf2c8c
-- title:
--   Act: right Actions
-- statement:
--   The Act construction uses the right Actions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModularGroupRowVecAndConjRightActions.lean#L41-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModularGroupRowVecAndConjRightActions.lean#L41-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActions
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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.Act
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate

theorem GlobalTheory.WpFam.Act.rightActions : ∀ (N : ℕ), _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.vact N) ∧ (∀ D, _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.WpFam.vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul (M • x) α = M • _root_.GlobalTheory.WpFam.vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ) ∧ _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by sorry

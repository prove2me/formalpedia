-- Prove2me | Theorems.Thm_GlobalTheory_T_qConj_torsion_points
-- name    : GlobalTheory.T.qConj_torsion_points
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:37:34.616353+00:00
-- url     : https://prove2.me/theorems/e9fbd2e0-6ed9-5e5c-96d8-24a26c71b0bf
-- title:
--   T: q Conj torsion points
-- statement:
--   The T construction uses the q Conj torsion points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QConjTorsionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QConjTorsionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QConjTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QConjTorsionStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.qConj_torsion_points : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), ZetaAct g N a → ∀ x : Fin 2 → ZMod N, QConj g N (wp N x) (wp N (vmul x (dg a))) ∧ QConj g N (wpd N x) (wpd N (vmul x (dg a))) ∧ (x ≠ 0 → QConj g N (wB N x) (wB N (vmul x (dg a)))) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_ConjExp_qConj_torsion
-- name    : GlobalTheory.WpFam.ConjExp.qConj_torsion
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:43.404322+00:00
-- url     : https://prove2.me/theorems/10c67b04-a2cc-475c-9f90-a52d45c2b998
-- title:
--   Conj Exp: q Conj torsion
-- statement:
--   The Conj Exp construction uses the q Conj torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QConjTorsion.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QConjTorsion.lean#L16-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexAutomorphismWeierstrassTorsionQCoeffs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedWeierstrassPTorsionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QConjTorsion
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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.ConjExp
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate

theorem GlobalTheory.WpFam.ConjExp.qConj_torsion : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wp N x) (_root_.GlobalTheory.WpFam.wp N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wpd N x) (_root_.GlobalTheory.WpFam.wpd N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ (x ≠ 0 → _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wB N x) (_root_.GlobalTheory.WpFam.wB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)))) := by sorry

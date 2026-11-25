-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_glConjugate_lastBasisNormalForm_of_ne_zero
-- name    : GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:18.851476+00:00
-- url     : https://prove2.me/theorems/35217a20-d01a-4307-89d6-b7e030c81d50
-- title:
--   T: exists gl Conjugate last Basis Normal Form of ne zero
-- statement:
--   The T construction uses the exists gl Conjugate last Basis Normal Form of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 → ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_T_operatorEab_preserves_smooth_classCC
-- name    : GlobalTheory.T.operatorEab_preserves_smooth_classCC
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:32.717058+00:00
-- url     : https://prove2.me/theorems/f79769c5-645b-42f3-97b4-1c25022766ed
-- title:
--   T: operator Eab preserves smooth class CC
-- statement:
--   The T construction uses the operator Eab preserves smooth class CC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OperatorEabPreservesSmoothClassCCStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OperatorEabPreservesSmoothClassCCStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OperatorEabPreservesSmoothClassCC
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OperatorEabPreservesSmoothClassCCStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.operatorEab_preserves_smooth_classCC : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by sorry

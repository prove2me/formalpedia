-- Prove2me | Theorems.Thm_GlobalTheory_tensorStd_rel_adjoint_splitCasimir
-- name    : GlobalTheory.tensorStd_rel_adjoint_splitCasimir
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:51.903701+00:00
-- url     : https://prove2.me/theorems/b1e9db70-fbd4-58a1-b7b1-c9b5b2f2b935
-- title:
--   Global Theory: tensor Std rel adjoint split Casimir
-- statement:
--   The Global Theory construction uses the tensor Std rel adjoint split Casimir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorStdRelAdjointSplitCasimir.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorStdRelAdjointSplitCasimir.lean#L7-L47

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorStdRelAdjointSplitCasimir
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory

theorem GlobalTheory.tensorStd_rel_adjoint_splitCasimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by sorry

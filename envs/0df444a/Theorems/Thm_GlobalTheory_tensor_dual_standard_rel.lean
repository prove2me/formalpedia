-- Prove2me | Theorems.Thm_GlobalTheory_tensor_dual_standard_rel
-- name    : GlobalTheory.tensor_dual_standard_rel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:51:46.768167+00:00
-- url     : https://prove2.me/theorems/16b130b2-5411-58a8-bd45-caf6604e868e
-- title:
--   Global Theory: tensor dual standard rel
-- statement:
--   The Global Theory construction uses the tensor dual standard rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorDualStandardRel.lean#L7-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorDualStandardRel.lean#L7-L46

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorDualStandardRel
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

theorem GlobalTheory.tensor_dual_standard_rel : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), _root_.Formalism.REAL.GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → _root_.Formalism.REAL.GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by sorry

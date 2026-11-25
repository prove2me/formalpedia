-- Prove2me | Theorems.Thm_GlobalTheory_splitCasimirStd_eigenvalue
-- name    : GlobalTheory.splitCasimirStd_eigenvalue
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:41.391505+00:00
-- url     : https://prove2.me/theorems/2c6af749-11dd-5815-8f79-cef3e9dc3857
-- title:
--   Global Theory: split Casimir Std eigenvalue
-- statement:
--   The Global Theory construction uses the split Casimir Std eigenvalue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirStdEigenvalue.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirStdEigenvalue.lean#L9-L30

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliComatrixLastRowInvertsCasimirStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorStdRelAdjointSplitCasimir
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirStdEigenvalue
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_lam

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

theorem GlobalTheory.splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by sorry

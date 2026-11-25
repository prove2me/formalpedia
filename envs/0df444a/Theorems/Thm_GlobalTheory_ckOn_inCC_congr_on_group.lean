-- Prove2me | Theorems.Thm_GlobalTheory_ckOn_inCC_congr_on_group
-- name    : GlobalTheory.ckOn_inCC_congr_on_group
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:55:26.073963+00:00
-- url     : https://prove2.me/theorems/cdeb83ce-cc22-5a3b-ab18-4123e51dc2cd
-- title:
--   Global Theory: ck On in CC congr on group
-- statement:
--   The Global Theory construction uses the ck On in CC congr on group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CkOnInCCCongrOnGroup.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CkOnInCCCongrOnGroup.lean#L76-L87

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CkOnInCCCongrOnGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
open GlobalTheory

theorem GlobalTheory.ckOn_inCC_congr_on_group : ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F F' : B.Mat k r → E), (∀ g ∈ B.GV k r, F g = F' g) → (B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F') ∧ ∀ m : ℕ, B.InCC A m F → B.InCC A m F' := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_EabClass_rdV_class
-- name    : GlobalTheory.EabClass.rdV_class
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:04.55399+00:00
-- url     : https://prove2.me/theorems/1ba90319-bc59-568e-ae67-c89b877927e0
-- title:
--   Eab Class: rd V class
-- statement:
--   The Eab Class construction uses the rd V class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OperatorEabPreservesSmoothClassCC.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/OperatorEabPreservesSmoothClassCC.lean#L13-L17

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OperatorEabPreservesSmoothClassCC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
open GlobalTheory GlobalTheory.EabClass

theorem GlobalTheory.EabClass.rdV_class {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {X : B.Mat k r}
    (hX : B.inLie k r X) {f : B.Mat k r → E} (hf : B.CkOn ⊤ (B.GV k r) f ∧ ∀ m : ℕ, B.InCC A m f) :
    B.CkOn ⊤ (B.GV k r) (RdV X f) ∧ ∀ m : ℕ, B.InCC A m (RdV X f) := by sorry

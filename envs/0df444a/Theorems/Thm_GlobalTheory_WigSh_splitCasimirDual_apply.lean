-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_splitCasimirDual_apply
-- name    : GlobalTheory.WigSh.splitCasimirDual_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:48:24.113319+00:00
-- url     : https://prove2.me/theorems/26c2c064-fb11-5c8c-9901-c3c0d4a4d0bc
-- title:
--   Wig Sh: split Casimir Dual apply
-- statement:
--   The Wig Sh construction uses the split Casimir Dual apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PieriLoweringStepGlTensorDualStandard.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PieriLoweringStepGlTensorDualStandard.lean#L27-L29

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenspaceIrreducibleDualStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReducedWignerCoefficientLoweringStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WignerExtremeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PieriLoweringStepGlTensorDualStandard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
noncomputable section
open GlobalTheory GlobalTheory.WigSh

theorem GlobalTheory.WigSh.splitCasimirDual_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (y : PiLp 2 (fun _ : Fin (n + 1) => V))
    (a : Fin (n + 1)) : splitCasimirDual E y a = ∑ c, E a c (y c) := by sorry

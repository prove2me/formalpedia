-- Prove2me | Theorems.Thm_GlobalTheory_splitCasimir_eigenspace_irreducible_standard
-- name    : GlobalTheory.splitCasimir_eigenspace_irreducible_standard
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:11.604039+00:00
-- url     : https://prove2.me/theorems/205ab79d-506c-41d2-9662-203774a9b66a
-- title:
--   Global Theory: split Casimir eigenspace irreducible standard
-- statement:
--   The Global Theory construction uses the split Casimir eigenspace irreducible standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirEigenspaceIrreducibleStandard.lean#L12-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SplitCasimirEigenspaceIrreducibleStandard.lean#L12-L124

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HighestWeightTensorStandard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorStdRelAdjointSplitCasimir
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenspaceIrreducibleStandard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
open GlobalTheory

theorem GlobalTheory.splitCasimir_eigenspace_irreducible_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + 0)) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + 0) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + 0)) ∧ Module.End.eigenspace Om (β + L l + 0) ≤ CapSp Et (shf β (Function.update L l (L l + 1))) := by sorry

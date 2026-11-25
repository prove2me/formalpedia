-- Prove2me | Theorems.Thm_GlobalTheory_starProjection_splitCasimirStd_last
-- name    : GlobalTheory.starProjection_splitCasimirStd_last
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:55:40.282803+00:00
-- url     : https://prove2.me/theorems/2ee5db38-25d3-4cb2-8496-3da1083826be
-- title:
--   Global Theory: star Projection split Casimir Std last
-- statement:
--   The Global Theory construction uses the star Projection split Casimir Std last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/StarProjectionSplitCasimirRaisingLast.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/StarProjectionSplitCasimirRaisingLast.lean#L13-L37

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorStdRelAdjointSplitCasimir
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliComatrixLastRowInvertsCasimir
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirStdEigenvalue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_StarProjectionSplitCasimirRaisingLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open GlobalTheory

theorem GlobalTheory.starProjection_splitCasimirStd_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by sorry

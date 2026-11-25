-- Prove2me | Theorems.Thm_GlobalTheory_reducedWigner_lowering
-- name    : GlobalTheory.reducedWigner_lowering
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:11:37.821102+00:00
-- url     : https://prove2.me/theorems/32c82954-9521-5584-bd15-ed28dd04af19
-- title:
--   Global Theory: reduced Wigner lowering
-- statement:
--   The Global Theory construction uses the reduced Wigner lowering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReducedWignerCoefficientLowering.lean#L14-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReducedWignerCoefficientLowering.lean#L14-L53

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LastComatrixRowInvertsDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenvalueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorDualStandardRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReducedWignerCoefficientLowering
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

theorem GlobalTheory.reducedWigner_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + (n : ℂ))).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by sorry

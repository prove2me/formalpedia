-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_mPlus_of_good_tangents
-- name    : GlobalTheory.MainTerm.mPlus_of_good_tangents
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:33.054743+00:00
-- url     : https://prove2.me/theorems/1fb0c79e-8876-4a45-87b6-7eddae4fc973
-- title:
--   Main Term: m Plus of good tangents
-- statement:
--   The Main Term construction uses the m Plus of good tangents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeSubMainTermIntegralLowBidegree.lean#L75-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeSubMainTermIntegralLowBidegree.lean#L75-L182

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearSubstCoordinateIntegralOfDegreeLtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRenameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeSubMainTermIntegralLowBidegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.MainTerm

theorem GlobalTheory.MainTerm.mPlus_of_good_tangents : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by sorry

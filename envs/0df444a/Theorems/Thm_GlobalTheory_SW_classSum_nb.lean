-- Prove2me | Theorems.Thm_GlobalTheory_SW_classSum_nb
-- name    : GlobalTheory.SW.classSum_nb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:35.746829+00:00
-- url     : https://prove2.me/theorems/57ff62ca-3d41-4968-b520-004e4ea3c847
-- title:
--   SW: class Sum nb
-- statement:
--   The SW construction uses the class Sum nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L229-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ClassSumNb.lean#L229-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open NbAvg

theorem GlobalTheory.SW.classSum_nb :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → ∀ f : Lt E n → ℂ, (∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ) → ((q : ℂ) - 1) * classSum M (fun Λ => ∑ᶠ Λ' ∈ Nb M P Λ, f Λ') = ((q : ℂ) ^ n - 1) * classSum M f := by sorry

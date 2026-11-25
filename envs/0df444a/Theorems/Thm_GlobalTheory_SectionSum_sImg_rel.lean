-- Prove2me | Theorems.Thm_GlobalTheory_SectionSum_sImg_rel
-- name    : GlobalTheory.SectionSum.sImg_rel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:54:15.932455+00:00
-- url     : https://prove2.me/theorems/72916b40-6bee-515f-905c-253d21525b36
-- title:
--   Section Sum: s Img rel
-- statement:
--   The Section Sum construction uses the s Img rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L115-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.SectionSum
open MvPolynomial MeasureTheory

theorem GlobalTheory.SectionSum.sImg_rel {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin D) :
    sImg (D := D) j₀ x (i.succ, j₀) +
      ∑ k, sImg (D := D) j₀ x (i.succ, j₀.succAbove k) * algebraMap Ω (OmS Ω D N) (x k) = 0 := by sorry

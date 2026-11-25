-- Prove2me | Theorems.Thm_GlobalTheory_SectionSum_exists_ae_cons
-- name    : GlobalTheory.SectionSum.exists_ae_cons
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:01:18.119921+00:00
-- url     : https://prove2.me/theorems/ca7fbfbb-226f-4602-9ea1-971754de4d7a
-- title:
--   Section Sum: exists ae cons
-- statement:
--   The Section Sum construction uses the exists ae cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L103-L113

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

theorem GlobalTheory.SectionSum.exists_ae_cons {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (hμ : μ ≠ 0)
    (D : ℕ) (p : (Fin (D + 1) → α) → Prop)
    (hp : ∀ᵐ t ∂(Measure.pi fun _ : Fin (D + 1) => μ), p t) :
    ∃ t₀ : α, ∀ᵐ t ∂(Measure.pi fun _ : Fin D => μ), p (Fin.cons t₀ t) := by sorry

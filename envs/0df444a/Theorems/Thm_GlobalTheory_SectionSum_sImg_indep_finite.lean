-- Prove2me | Theorems.Thm_GlobalTheory_SectionSum_sImg_indep_finite
-- name    : GlobalTheory.SectionSum.sImg_indep_finite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:54:07.540003+00:00
-- url     : https://prove2.me/theorems/82c33346-a95c-4985-a613-1c049b23ead0
-- title:
--   Section Sum: s Img indep finite
-- statement:
--   The Section Sum construction uses the s Img indep finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L17-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L17-L44

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

theorem GlobalTheory.SectionSum.sImg_indep_finite (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] (D N : ℕ)
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (hfg : (⊤ : IntermediateField K Ω).FG)
    (htr : Algebra.trdeg K Ω = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent Ω fun k => KaehlerDifferential.D K Ω (x (J k))) :
    Function.Injective (sHom (K := K) (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
        (OmS Ω D N) := by sorry

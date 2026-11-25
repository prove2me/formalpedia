-- Prove2me | Theorems.Thm_GlobalTheory_SectionSum_bijOn_restrict
-- name    : GlobalTheory.SectionSum.bijOn_restrict
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:00:17.775605+00:00
-- url     : https://prove2.me/theorems/a9e72a6f-10bc-559f-8b79-014839789814
-- title:
--   Section Sum: bij On restrict
-- statement:
--   The Section Sum construction uses the bij On restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L125-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L125-L173

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

theorem GlobalTheory.SectionSum.bijOn_restrict {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hext : ∀ Q : Ω →+* ℂ, Q ∈ PT (Ω := Ω) sg →
      (∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0) →
      ∃! P : OmS Ω D N →+* ℂ, (∀ a : Ω, P (algebraMap Ω (OmS Ω D N) a) = Q a) ∧
        ∀ p, P (sImg j₀ x p) = pt p) :
    Set.BijOn (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N)))
      {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p}
      {Q | Q ∈ PT (Ω := Ω) sg ∧
        ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by sorry

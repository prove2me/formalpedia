-- Prove2me | Theorems.Thm_GlobalTheory_BoxCosetSum_eq_sum_finprod_box_indicator
-- name    : GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:01:17.00557+00:00
-- url     : https://prove2.me/theorems/dbf34ac1-8d44-4115-8150-3102f8967171
-- title:
--   Box Coset Sum: eq sum finprod box indicator
-- statement:
--   The Box Coset Sum construction uses the eq sum finprod box indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L127-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L127-L190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by sorry

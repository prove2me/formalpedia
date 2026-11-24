-- Prove2me | Theorems.Thm_GlobalTheory_BoxCosetSum_finprod_indicator_eq
-- name    : GlobalTheory.BoxCosetSum.finprod_indicator_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:02:39.042775+00:00
-- url     : https://prove2.me/theorems/4b11c6e0-c482-4e77-ac1a-e691a931a130
-- title:
--   Box Coset Sum: finprod indicator eq
-- statement:
--   The Box Coset Sum construction uses the finprod indicator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L83-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L83-L125

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

theorem GlobalTheory.BoxCosetSum.finprod_indicator_eq (κ : Type) [Finite κ]
    (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F)
    (r y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))) =
      Set.indicator {z | z - r ∈ boxSub κ B} (fun _ => (1 : ℂ)) y := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_BoxCosetSum_isOpen_boxSub
-- name    : GlobalTheory.BoxCosetSum.isOpen_boxSub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:02:43.209325+00:00
-- url     : https://prove2.me/theorems/82440fb1-4594-4d9e-9ad8-f6486203ba7c
-- title:
--   Box Coset Sum: is Open box Sub
-- statement:
--   The Box Coset Sum construction uses the is Open box Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L70-L81

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

theorem GlobalTheory.BoxCosetSum.isOpen_boxSub (κ : Type) [Finite κ] (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by sorry

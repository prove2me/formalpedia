-- Prove2me | Theorems.Thm_GlobalTheory_mem_of_wild_of_pow_mem_open_normal
-- name    : GlobalTheory.mem_of_wild_of_pow_mem_open_normal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:54:49.833252+00:00
-- url     : https://prove2.me/theorems/fbed0cbe-9148-4cbb-b5f7-4138c117723d
-- title:
--   Global Theory: mem of wild of pow mem open normal
-- statement:
--   The Global Theory construction uses the mem of wild of pow mem open normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ValuationPowApplyDivSubOneLt.lean#L35-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ValuationPowApplyDivSubOneLt.lean#L35-L102

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ValuationPowApplyDivSubOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open GlobalTheory
open NumberField IsDedekindDomain

theorem GlobalTheory.mem_of_wild_of_pow_mem_open_normal :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ (H : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)), H.Normal → IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∀ (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) (n : ℕ), ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → σ ^ n ∈ H → σ ∈ H := by sorry

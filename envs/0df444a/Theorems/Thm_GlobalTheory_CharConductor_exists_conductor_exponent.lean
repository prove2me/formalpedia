-- Prove2me | Theorems.Thm_GlobalTheory_CharConductor_exists_conductor_exponent
-- name    : GlobalTheory.CharConductor.exists_conductor_exponent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:53.408701+00:00
-- url     : https://prove2.me/theorems/e3159c09-c899-49c2-8b4f-a29028a2896b
-- title:
--   Char Conductor: exists conductor exponent
-- statement:
--   The Char Conductor construction uses the exists conductor exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AdditiveCharConductorExists.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AdditiveCharConductorExists.lean#L32-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfNormSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CharConductor

theorem GlobalTheory.CharConductor.exists_conductor_exponent : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by sorry

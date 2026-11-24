-- Prove2me | Theorems.Thm_GlobalTheory_ConductorAdicCompletion_exists_conductor_adicCompletion
-- name    : GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:42.849903+00:00
-- url     : https://prove2.me/theorems/dd032ed6-341c-44f5-aac8-4e1ee0c256a4
-- title:
--   Conductor Adic Completion: exists conductor adic Completion
-- statement:
--   The Conductor Adic Completion construction uses the exists conductor adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsConductorAdicCompletion.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsConductorAdicCompletion.lean#L86-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConductorAdicCompletion

theorem GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (ψ : AddChar (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ℂ),
      Continuous (⇑ψ : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → ℂ) →
      (∀ t, ‖ψ t‖ = (1 : ℝ)) → (∃ t, ψ t ≠ (1 : ℂ)) →
      ∃ n : ℤ, ∀ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v,
        (∀ s ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v,
          ψ (t * s) = (1 : ℂ)) ↔
        (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v →
          WithZero (Multiplicative ℤ)) t ≤ WithZero.exp n := by sorry

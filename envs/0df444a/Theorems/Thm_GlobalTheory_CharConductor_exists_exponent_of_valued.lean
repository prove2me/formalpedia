-- Prove2me | Theorems.Thm_GlobalTheory_CharConductor_exists_exponent_of_valued
-- name    : GlobalTheory.CharConductor.exists_exponent_of_valued
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:01.043812+00:00
-- url     : https://prove2.me/theorems/fc7f32cd-cd98-4922-b8bc-31cb65d64feb
-- title:
--   Char Conductor: exists exponent of valued
-- statement:
--   The Char Conductor construction uses the exists exponent of valued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AdditiveCharConductorExists.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AdditiveCharConductorExists.lean#L20-L30

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

theorem GlobalTheory.CharConductor.exists_exponent_of_valued {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_DenseCompl_continuous_of_valued_eq
-- name    : GlobalTheory.DenseCompl.continuous_of_valued_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:27.943805+00:00
-- url     : https://prove2.me/theorems/79786a5d-6bea-4747-9408-9341e45d0eb6
-- title:
--   Dense Compl: continuous of valued eq
-- statement:
--   The Dense Compl construction uses the continuous of valued eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L74-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl

theorem GlobalTheory.DenseCompl.continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by sorry

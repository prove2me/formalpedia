-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LagFun_exists_param
-- name    : GlobalTheory.CompanionTheory.LagFun.exists_param
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:08.967922+00:00
-- url     : https://prove2.me/theorems/aad26e0d-38a0-4d34-aa6a-625cfafbcba7
-- title:
--   Lag Fun: exists param
-- statement:
--   The Lag Fun construction uses the exists param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsInvariantForm.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsInvariantForm.lean#L9-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LagFun

theorem GlobalTheory.CompanionTheory.LagFun.exists_param {k : Type} [Field k] {κ : Type} [Fintype κ] (large₂ : Submodule k ((κ → k) × (κ → k))) :
    ∃ (n : ℕ) (j σ : (Fin n → k) →ₗ[k] (κ → k)) (p : (κ → k) →ₗ[k] (Fin n → k)),
      (∀ t, p (j t) = t) ∧ (∀ t, (j t, σ t) ∈ large₂) ∧ ∀ w ∈ large₂, ∃ t, j t = w.1 := by sorry

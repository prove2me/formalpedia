-- Prove2me | Theorems.Thm_GlobalTheory_seminorm_formPerpVector_le
-- name    : GlobalTheory.seminorm_formPerpVector_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:03.168598+00:00
-- url     : https://prove2.me/theorems/42ebb801-ac7f-4c53-93d7-3ac50893a9dd
-- title:
--   Global Theory: seminorm form Perp Vector le
-- statement:
--   The Global Theory construction uses the seminorm form Perp Vector le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L273-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L273-L284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}

theorem GlobalTheory.seminorm_formPerpVector_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (h : M →ₗ[R] M →ₛₗ[σ] R) (hcs : ∀ u v, ν (h u v) ≤ μ u * μ v)
    (e e' : Fin p → M) (g : M) {r : ℝ}
    (he : ∀ a, μ (e a) ≤ r) (he' : ∀ a, μ (e' a) ≤ r) (hg : μ g ≤ r) :
    μ (formPerpVector h e e' g) ≤ (p + 1)! * r ^ (2 * p + 1) := by sorry

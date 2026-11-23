-- Prove2me | Theorems.Thm_GlobalTheory_seminorm_det_formPairMatrix_le
-- name    : GlobalTheory.seminorm_det_formPairMatrix_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:59.399825+00:00
-- url     : https://prove2.me/theorems/f86e945a-dbf4-4d6e-9601-1f9262fd4040
-- title:
--   Global Theory: seminorm det form Pair Matrix le
-- statement:
--   The Global Theory construction uses the seminorm det form Pair Matrix le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L286-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L286-L294

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

theorem GlobalTheory.seminorm_det_formPairMatrix_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (h : M →ₗ[R] M →ₛₗ[σ] R) (hcs : ∀ u v, ν (h u v) ≤ μ u * μ v)
    (e e' : Fin p → M) {r : ℝ} (he : ∀ a, μ (e a) ≤ r) (he' : ∀ a, μ (e' a) ≤ r) :
    ν (formPairMatrix h e e').det ≤ p ! * r ^ (2 * p) := by sorry

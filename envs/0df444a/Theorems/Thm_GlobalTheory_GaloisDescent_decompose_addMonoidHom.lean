-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_decompose_addMonoidHom
-- name    : GlobalTheory.GaloisDescent.decompose_addMonoidHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:55.764933+00:00
-- url     : https://prove2.me/theorems/4f3ce7ca-24bb-4815-a7f3-28e6478367a3
-- title:
--   Galois Descent: decompose add Monoid Hom
-- statement:
--   The Galois Descent construction uses the decompose add Monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L14-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']

theorem GlobalTheory.GaloisDescent.decompose_addMonoidHom (ℳ : ι → σ) (ℳ' : ι → τ) [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition ℳ'] (φ : M →+ M') (hφ : ∀ i, ∀ x ∈ ℳ i, φ x ∈ ℳ' i) (x : M) (i : ι) :
    (DirectSum.decompose ℳ' (φ x) i : M') = φ (DirectSum.decompose ℳ x i) := by sorry

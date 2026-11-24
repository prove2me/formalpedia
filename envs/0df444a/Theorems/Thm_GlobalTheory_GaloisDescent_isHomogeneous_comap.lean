-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_isHomogeneous_comap
-- name    : GlobalTheory.GaloisDescent.isHomogeneous_comap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:47:52.748007+00:00
-- url     : https://prove2.me/theorems/1d8b8a15-eadb-436d-b353-fc0399c498af
-- title:
--   Galois Descent: is Homogeneous comap
-- statement:
--   The Galois Descent construction uses the is Homogeneous comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L74-L76

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
variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}
variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]

theorem GlobalTheory.GaloisDescent.isHomogeneous_comap (h : ∀ i, ∀ a ∈ 𝒜 i, j a ∈ ℬ i) {I : Ideal B}
    (hI : I.IsHomogeneous ℬ) : (I.comap j).IsHomogeneous 𝒜 := by sorry

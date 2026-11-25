-- Prove2me | Theorems.Thm_GlobalTheory_EigenLine_line_hyperplane_cut
-- name    : GlobalTheory.EigenLine.line_hyperplane_cut
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:16.299799+00:00
-- url     : https://prove2.me/theorems/499a615d-01bc-58fa-8f8a-c08a492a8070
-- title:
--   Eigen Line: line hyperplane cut
-- statement:
--   The Eigen Line construction uses the line hyperplane cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LineHyperplaneCut.lean#L72-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LineHyperplaneCut.lean#L72-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.EigenLine
variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]

theorem GlobalTheory.EigenLine.line_hyperplane_cut (K : Type) [Field K] (O : Type) [CommRing O] (L : Type)
    [AddCommGroup L] [Module K L]
    [FiniteDimensional K L] (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (χ : O →+* K) (ε : K ⊗[ℤ] O) (M M' : Submodule K L) (n₀ : L)
    (hcc : ∀ a, c (c a) = a) (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (hε0 : ε ≠ 0) (hMM : IsCompl M M')
    (hM : ∀ a, ∀ x ∈ M, ρ a x ∈ M) (hM' : ∀ a, ∀ x ∈ M', ρ a x ∈ M')
    (hspan : M = Submodule.span K (Set.range fun a => ρ a n₀))
    (hinj : ∀ t : K ⊗[ℤ] O, tensorAction ρ t n₀ = 0 → t = 0) :
    Module.finrank K ↥(M ⊓ LinearMap.range (tensorAction ρ ε)) = 1 ∧
    Module.finrank K ↥(B.orthogonal M ⊓ LinearMap.range (tensorAction ρ ε)) + 1 =
      Module.finrank K ↥(LinearMap.range (tensorAction ρ ε)) := by sorry

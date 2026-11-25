-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_ringKrullDim_cone
-- name    : GlobalTheory.TorsionZero.ringKrullDim_cone
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:45.912178+00:00
-- url     : https://prove2.me/theorems/199f79d1-a900-437a-a859-2642b3258127
-- title:
--   Torsion Zero: ring Krull Dim cone
-- statement:
--   The Torsion Zero construction uses the ring Krull Dim cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L104-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L104-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]

theorem GlobalTheory.TorsionZero.ringKrullDim_cone {T C : Type} [CommRing T] [IsDomain T] [Algebra K T]
    [Algebra.FiniteType K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] [Finite σ] {x : σ → T}
    (hx : ∀ j, x j ∈ 𝒜 1) [Algebra.IsIntegral (Algebra.adjoin K (Set.range x)) T]
    [CommRing C] [IsDomain C] [Algebra K C] (r : σ → C) (i : σ) (hi : r i = 1)
    (hr : Function.Surjective (aeval r : MvPolynomial σ K →ₐ[K] C))
    (hrel : ∀ n (G : MvPolynomial σ K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0))
    (g : ℕ) (hg : ringKrullDim C = g) : ringKrullDim T = (g + 1 : ℕ) := by sorry

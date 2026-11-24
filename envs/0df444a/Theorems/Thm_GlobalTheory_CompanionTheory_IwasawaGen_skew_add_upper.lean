-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwasawaGen_skew_add_upper
-- name    : GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:53.096599+00:00
-- url     : https://prove2.me/theorems/71c70dba-d840-480e-89d8-de136268964f
-- title:
--   Iwasawa Gen: skew add upper
-- statement:
--   The Iwasawa Gen construction uses the skew add upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CartanDecompositionLieAlgebra.lean#L6-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CartanDecompositionLieAlgebra.lean#L6-L77

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CartanDecompositionLieAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwasawaGen

theorem GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hanti : Antitone h)
    (hf : ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hreg : ∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) :
    ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by sorry

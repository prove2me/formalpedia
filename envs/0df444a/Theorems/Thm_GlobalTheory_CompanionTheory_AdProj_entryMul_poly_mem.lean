-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdProj_entryMul_poly_mem
-- name    : GlobalTheory.CompanionTheory.AdProj.entryMul_poly_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:16:17.891252+00:00
-- url     : https://prove2.me/theorems/15543c16-6233-4608-a101-4b37dbb924af
-- title:
--   Ad Proj: entry Mul poly mem
-- statement:
--   The Ad Proj construction uses the entry Mul poly mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraFunctionCalculus.lean#L42-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraFunctionCalculus.lean#L42-L66

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdProj

theorem GlobalTheory.CompanionTheory.AdProj.entryMul_poly_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (p : Polynomial ℝ) :
    entryMul h (fun t => p.eval t) X ∈ 𝔤 := by sorry

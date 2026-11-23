-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_CentreBlocks_isIntegral_eval
-- name    : GlobalTheory.CompanionTheory.Dblock.CentreBlocks.isIntegral_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:21.112726+00:00
-- url     : https://prove2.me/theorems/5aee4884-1b5f-4f19-bfd9-07374c3e476b
-- title:
--   Centre Blocks: is Integral eval
-- statement:
--   The Centre Blocks construction uses the is Integral eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdeal.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdeal.lean#L61-L66

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.CentreBlocks
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.Dblock.CentreBlocks.isIntegral_eval {A : Type} [CommRing A] [Algebra ℂ A] (P : A[X])
    (h : ∀ k, IsIntegral ℂ (P.coeff k)) (x : A) (hx : IsIntegral ℂ x) :
    IsIntegral ℂ (P.eval x) := by sorry

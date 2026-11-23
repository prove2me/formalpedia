-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_CentreBlocks_sumPoly_monic
-- name    : GlobalTheory.CompanionTheory.Dblock.CentreBlocks.sumPoly_monic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:59.467602+00:00
-- url     : https://prove2.me/theorems/65ebc7bd-0007-4664-8003-d5013a3c5edd
-- title:
--   Centre Blocks: sum Poly monic
-- statement:
--   The Centre Blocks construction uses the sum Poly monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdeal.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdeal.lean#L83-L89

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

theorem GlobalTheory.CompanionTheory.Dblock.CentreBlocks.sumPoly_monic {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) (h : c n = 1) :
    (sumPoly c n).Monic := by sorry

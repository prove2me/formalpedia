-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_CentreBlocks_sumPoly_coeff
-- name    : GlobalTheory.CompanionTheory.Dblock.CentreBlocks.sumPoly_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:19.431812+00:00
-- url     : https://prove2.me/theorems/15068048-3117-40f0-b192-0967a31195c2
-- title:
--   Centre Blocks: sum Poly coeff
-- statement:
--   The Centre Blocks construction uses the sum Poly coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdeal.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CapelliPolynomialCoefficientsIdeal.lean#L79-L81

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

theorem GlobalTheory.CompanionTheory.Dblock.CentreBlocks.sumPoly_coeff {A : Type} [CommRing A] (c : ℕ → A) (n m : ℕ) :
    (sumPoly c n).coeff m = if m < n + 1 then c m else 0 := by sorry

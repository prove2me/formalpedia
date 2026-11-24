-- Prove2me | Theorems.Thm_GlobalTheory_IterDProd_hasLineDerivAt_prod
-- name    : GlobalTheory.IterDProd.hasLineDerivAt_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:23:56.643518+00:00
-- url     : https://prove2.me/theorems/17d7e122-0aca-4d27-b210-ee735755f8e5
-- title:
--   Iter DProd: has Line Deriv At prod
-- statement:
--   The Iter DProd construction uses the has Line Deriv At prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedPartialDerivProdOneVarAtZero.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedPartialDerivProdOneVarAtZero.lean#L17-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivProdOneVarAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.IterDProd

theorem GlobalTheory.IterDProd.hasLineDerivAt_prod {I : Type} [Fintype I] [DecidableEq I] (φ : I → ℂ → ℂ) (A : ℂ)
    (z : I → ℂ) (j : I) (hj : DifferentiableAt ℂ (φ j) (z j)) :
    HasLineDerivAt ℂ (fun z : I → ℂ ↦ A * ∏ i, φ i (z i))
      (A * (deriv (φ j) (z j) * ∏ i ∈ Finset.univ.erase j, φ i (z i))) z (Pi.single j 1) := by sorry

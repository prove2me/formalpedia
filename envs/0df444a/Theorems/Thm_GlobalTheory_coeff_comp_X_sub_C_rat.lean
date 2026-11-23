-- Prove2me | Theorems.Thm_GlobalTheory_coeff_comp_X_sub_C_rat
-- name    : GlobalTheory.coeff_comp_X_sub_C_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:08.952417+00:00
-- url     : https://prove2.me/theorems/1e892d0b-8ce3-4d37-b15b-fe5ad4979463
-- title:
--   Global Theory: coeff comp X sub C rat
-- statement:
--   The Global Theory construction uses the coeff comp X sub C rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L215-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L215-L220

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]

theorem GlobalTheory.coeff_comp_X_sub_C_rat {P : ℚ[X]} {e : ℕ} (h : P.degree ≤ e) (r : ℚ) :
    (P.comp (Polynomial.X - Polynomial.C r)).coeff e = P.coeff e := by sorry

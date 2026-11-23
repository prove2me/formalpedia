-- Prove2me | Theorems.Thm_GlobalTheory_exists_form_lt_sup_lt_colon
-- name    : GlobalTheory.exists_form_lt_sup_lt_colon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:01.17848+00:00
-- url     : https://prove2.me/theorems/a5d2a748-eeac-421c-a937-46028ec367e3
-- title:
--   Global Theory: exists form lt sup lt colon
-- statement:
--   The Global Theory construction uses the exists form lt sup lt colon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L199-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L199-L209

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
omit [Finite ι]

theorem GlobalTheory.exists_form_lt_sup_lt_colon {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (h : I ≠ ⊤) (hp : ¬ I.IsPrime) :
    ∃ (d : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous d ∧ I < I ⊔ Ideal.span {f} ∧
      I < Submodule.colon I {f} := by sorry

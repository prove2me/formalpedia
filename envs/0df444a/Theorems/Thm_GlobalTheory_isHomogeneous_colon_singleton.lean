-- Prove2me | Theorems.Thm_GlobalTheory_isHomogeneous_colon_singleton
-- name    : GlobalTheory.isHomogeneous_colon_singleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:52.123192+00:00
-- url     : https://prove2.me/theorems/22e6c133-701c-436c-8fb7-c3bfe9ac469e
-- title:
--   Global Theory: is Homogeneous colon singleton
-- statement:
--   The Global Theory construction uses the is Homogeneous colon singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L78-L85

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

theorem GlobalTheory.isHomogeneous_colon_singleton {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (Submodule.colon I {f}).IsHomogeneous (homogeneousSubmodule ι k) := by sorry

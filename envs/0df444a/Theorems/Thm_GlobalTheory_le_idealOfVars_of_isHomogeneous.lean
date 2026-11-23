-- Prove2me | Theorems.Thm_GlobalTheory_le_idealOfVars_of_isHomogeneous
-- name    : GlobalTheory.le_idealOfVars_of_isHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:28.084193+00:00
-- url     : https://prove2.me/theorems/2ad79394-9c9e-4103-9f16-7eaddf955e72
-- title:
--   Global Theory: le ideal Of Vars of is Homogeneous
-- statement:
--   The Global Theory construction uses the le ideal Of Vars of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L102-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L102-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*}

theorem GlobalTheory.le_idealOfVars_of_isHomogeneous {k : Type*} [Field k] {J : Ideal (MvPolynomial σ k)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (hJ' : J ≠ ⊤) : J ≤ idealOfVars σ k := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_residue_valuationSubring_ne_zero_iff
-- name    : GlobalTheory.residue_valuationSubring_ne_zero_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:55:22.757075+00:00
-- url     : https://prove2.me/theorems/b47c0766-11c0-47ec-bd17-cc9eb24467d3
-- title:
--   Global Theory: residue valuation Subring ne zero iff
-- statement:
--   The Global Theory construction uses the residue valuation Subring ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraicIndependentResidueIffGauss.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraicIndependentResidueIffGauss.lean#L8-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraicIndependentResidueIffGauss
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

theorem GlobalTheory.residue_valuationSubring_ne_zero_iff {U Γ : Type*} [Field U]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ) (x : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring x ≠ 0 ↔ v (x : U) = 1 := by sorry

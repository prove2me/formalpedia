-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_mem_subGrading
-- name    : GlobalTheory.TorsionZero.mem_subGrading
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:44.718732+00:00
-- url     : https://prove2.me/theorems/c2bfd5d1-c56b-420f-add2-1a36e8463d1e
-- title:
--   Torsion Zero: mem sub Grading
-- statement:
--   The Torsion Zero construction uses the mem sub Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L172-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L172-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

theorem GlobalTheory.TorsionZero.mem_subGrading {𝒜 : ℕ → Submodule K R} {N : ℕ} {T : Subalgebra K R} {e : ℕ} {y : T} :
    y ∈ subGrading 𝒜 N T e ↔ (y : R) ∈ 𝒜 (N * e) := by sorry

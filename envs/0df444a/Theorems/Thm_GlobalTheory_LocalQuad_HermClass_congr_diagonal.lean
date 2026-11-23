-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_HermClass_congr_diagonal
-- name    : GlobalTheory.LocalQuad.HermClass.congr_diagonal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:59.012071+00:00
-- url     : https://prove2.me/theorems/2487bd27-2ad6-4d48-8ac9-fcf8100170b3
-- title:
--   Herm Class: congr diagonal
-- statement:
--   The Herm Class construction uses the congr diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L245-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L245-L288

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.LocalQuad.HermClass.congr_diagonal (H : Isotropy) (r : ℕ) : ∀ g g' : Fin r → E,
    (∀ i, cc (g i) = g i) → (∀ i, cc (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∀ τ : E →+* ℂ, posCount τ g = posCount τ g') →
    (∃ x : E, ∏ i, g i = x * cc x * ∏ i, g' i) →
    Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal g') := by sorry

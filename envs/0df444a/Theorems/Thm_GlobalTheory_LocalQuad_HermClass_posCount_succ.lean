-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_HermClass_posCount_succ
-- name    : GlobalTheory.LocalQuad.HermClass.posCount_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:37.358366+00:00
-- url     : https://prove2.me/theorems/e3d862e9-5c45-45fe-ba67-328d15d1c27a
-- title:
--   Herm Class: pos Count succ
-- statement:
--   The Herm Class construction uses the pos Count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L205-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L205-L207

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
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.LocalQuad.HermClass.posCount_succ (τ : E →+* ℂ) {r : ℕ} (g : Fin (r + 1) → E) :
    posCount τ g = (if 0 < (τ (g 0)).re then 1 else 0) + posCount τ fun i : Fin r => g i.succ := by sorry

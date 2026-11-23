-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_HermClass_exists_sign_iff
-- name    : GlobalTheory.LocalQuad.HermClass.exists_sign_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:35.331674+00:00
-- url     : https://prove2.me/theorems/b520f555-45f2-448f-bdf3-4a2b19b3819d
-- title:
--   Herm Class: exists sign iff
-- statement:
--   The Herm Class construction uses the exists sign iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L222-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L222-L243

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

theorem GlobalTheory.LocalQuad.HermClass.exists_sign_iff (τ : E →+* ℂ) {r : ℕ} {g g' : Fin r → E}
    (h : posCount τ g = posCount τ g') (j : Fin r) :
    ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ (g' j)).re) := by sorry

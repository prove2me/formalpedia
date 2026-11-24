-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_exists_extension_line
-- name    : GlobalTheory.TorusConst.exists_extension_line
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:52.176891+00:00
-- url     : https://prove2.me/theorems/589cd8c4-0409-453e-a82f-55b653f23dc1
-- title:
--   Torus Const: exists extension line
-- statement:
--   The Torus Const construction uses the exists extension line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L387-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L387-L397

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
open LaurentPolynomial
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.TorusConst.exists_extension_line [IsProper B.hom] (u : sp K L[T;T⁻¹] ⟶ B) :
    ∃ b : sp K L[X] ⟶ B, spm (inc K L) ≫ b = u := by sorry

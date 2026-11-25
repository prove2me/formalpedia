-- Prove2me | Theorems.Thm_GlobalTheory_GrpSpread_exists_grpObj
-- name    : GlobalTheory.GrpSpread.exists_grpObj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:51:10.935019+00:00
-- url     : https://prove2.me/theorems/03609f25-bf2d-4c06-812f-8ca26ecb2927
-- title:
--   Grp Spread: exists grp Obj
-- statement:
--   The Grp Spread construction uses the exists grp Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjDescendsToFgSubalgebra.lean#L114-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjDescendsToFgSubalgebra.lean#L114-L205

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.GrpSpread
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

theorem GlobalTheory.GrpSpread.exists_grpObj (j : U ⟶ Z) [QuasiCompact j] [IsSchemeTheoreticallyDominant j] [Flat G.hom]
    [IsSeparated G.hom] [GrpObj A] [IsCommMonObj A] (h : IsPullback φ A.hom G.hom j)
    (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : sq h.w ≫ m.left = (μ[A]).left ≫ φ) (hi : φ ≫ i.left = (ι[A]).left ≫ φ)
    (he : j ≫ e.left = (η[A]).left ≫ φ) : ∃ _ : GrpObj G, IsCommMonObj G ∧ IsGrpPullback A G j φ := by sorry

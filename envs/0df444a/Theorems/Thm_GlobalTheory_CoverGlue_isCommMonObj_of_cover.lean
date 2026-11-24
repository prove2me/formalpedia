-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_isCommMonObj_of_cover
-- name    : GlobalTheory.CoverGlue.isCommMonObj_of_cover
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:27:30.172919+00:00
-- url     : https://prove2.me/theorems/b9873a8d-0803-4c48-ab36-84ab70df82d4
-- title:
--   Cover Glue: is Comm Mon Obj of cover
-- statement:
--   The Cover Glue construction uses the is Comm Mon Obj of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsAbelianSchemeAndRelDimOfOpenCover.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsAbelianSchemeAndRelDimOfOpenCover.lean#L23-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsAbelianSchemeAndRelDimOfOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue

theorem GlobalTheory.CoverGlue.isCommMonObj_of_cover {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    [GrpObj A] {G : ∀ i, Over (U i).toScheme} [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}
    (h : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (hc : ∀ i, IsCommMonObj (G i)) : IsCommMonObj A := by sorry

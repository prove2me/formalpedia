-- Prove2me | Theorems.Thm_GlobalTheory_FibreGrp_hom_ext_of_fibres
-- name    : GlobalTheory.FibreGrp.hom_ext_of_fibres
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:48:19.223989+00:00
-- url     : https://prove2.me/theorems/87117c1f-53e1-412e-a54e-4c149d8b7d00
-- title:
--   Fibre Grp: hom ext of fibres
-- statement:
--   The Fibre Grp construction uses the hom ext of fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjOfDenseFibres.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjOfDenseFibres.lean#L15-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjOfDenseFibres
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
open GlobalTheory GlobalTheory.FibreGrp

theorem GlobalTheory.FibreGrp.hom_ext_of_fibres {S : Scheme.{0}} [IsReduced S] {Sg : Set S} (hSg : Dense Sg) {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ p ∈ Sg, ∃ (U : Scheme.{0}) (j : U ⟶ S), p ∈ Set.range j ∧
      ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by sorry

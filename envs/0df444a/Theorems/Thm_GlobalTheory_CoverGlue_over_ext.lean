-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_over_ext
-- name    : GlobalTheory.CoverGlue.over_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:49.649206+00:00
-- url     : https://prove2.me/theorems/3ad4ee9c-1c4b-4376-bca4-751ff28de742
-- title:
--   Cover Glue: over ext
-- statement:
--   The Cover Glue construction uses the over ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueHom.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueHom.lean#L57-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
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
variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}

theorem GlobalTheory.CoverGlue.over_ext (hU : iSup U = ⊤) {T A : Over S} {f g : T ⟶ A}
    (h : ∀ i (T' : Over (U i).toScheme) (r : Over.mk (T'.hom ≫ (U i).ι) ⟶ T), r ≫ f = r ≫ g) : f = g := by sorry

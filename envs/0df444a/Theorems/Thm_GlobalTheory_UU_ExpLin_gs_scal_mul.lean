-- Prove2me | Theorems.Thm_GlobalTheory_UU_ExpLin_gs_scal_mul
-- name    : GlobalTheory.UU.ExpLin.gs_scal_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:57.57232+00:00
-- url     : https://prove2.me/theorems/f9f763d6-eb55-48d3-9c2a-a7b337140ed8
-- title:
--   Exp Lin: gs scal mul
-- statement:
--   The Exp Lin construction uses the gs scal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpFLinear.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpFLinear.lean#L25-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLin

theorem GlobalTheory.UU.ExpLin.gs_scal_mul {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (a b : R) : gs r z ⊤ (scal p (a * b)) = gs r z ⊤ (scal p a) * gs r z ⊤ (scal p b) := by sorry

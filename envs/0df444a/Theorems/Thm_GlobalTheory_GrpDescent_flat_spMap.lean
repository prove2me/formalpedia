-- Prove2me | Theorems.Thm_GlobalTheory_GrpDescent_flat_spMap
-- name    : GlobalTheory.GrpDescent.flat_spMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:22:53.213807+00:00
-- url     : https://prove2.me/theorems/4e4c9172-fe20-474e-ada9-814d52e2f6f9
-- title:
--   Grp Descent: flat sp Map
-- statement:
--   The Grp Descent construction uses the flat sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjDescendsToLargeSubfield.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjDescendsToLargeSubfield.lean#L123-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToLargeSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.GrpDescent
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

theorem GlobalTheory.GrpDescent.flat_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Flat (spMap β) := by sorry

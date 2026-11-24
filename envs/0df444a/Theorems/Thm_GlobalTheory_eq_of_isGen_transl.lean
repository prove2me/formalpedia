-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_isGen_transl
-- name    : GlobalTheory.eq_of_isGen_transl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:55.176327+00:00
-- url     : https://prove2.me/theorems/a1ce3521-38f7-4851-96b8-e1d79b8879e5
-- title:
--   Global Theory: eq of is Gen transl
-- statement:
--   The Global Theory construction uses the eq of is Gen transl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOfIsGenTransl.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOfIsGenTransl.lean#L13-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIsGenOfInvariant
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOfIsGenTransl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.eq_of_isGen_transl : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b b' : TF (R := R) F ⟶ D.P.A) (r : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] ![1, -1])), r.IsGen → b = b' := by sorry

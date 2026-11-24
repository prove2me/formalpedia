-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlat_flat_of_flatOver
-- name    : GlobalTheory.FibreFlat.flat_of_flatOver
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:14.02325+00:00
-- url     : https://prove2.me/theorems/7e70b940-cb0c-4f00-be16-a6efb8363784
-- title:
--   Fibre Flat: flat of flat Over
-- statement:
--   The Fibre Flat construction uses the flat of flat Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L145-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L145-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing
open GlobalTheory
open GlobalTheory.FibreFlat
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.FibreFlat.flat_of_flatOver (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp T)
    (h1 : Flat (f ≫ g)) (h2 : LocallyOfFiniteType (f ≫ g)) (h3 : LocallyOfFiniteType g)
    (hK : FlatOver f g (spMap (algebraMap T K))) (hκ : FlatOver f g (spMap (residue T))) :
    Flat f := by sorry

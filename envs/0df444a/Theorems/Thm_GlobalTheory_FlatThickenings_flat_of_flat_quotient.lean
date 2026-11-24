-- Prove2me | Theorems.Thm_GlobalTheory_FlatThickenings_flat_of_flat_quotient
-- name    : GlobalTheory.FlatThickenings.flat_of_flat_quotient
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:01.974095+00:00
-- url     : https://prove2.me/theorems/b18bb131-bc08-419a-9fc6-d91e16558773
-- title:
--   Flat Thickenings: flat of flat quotient
-- statement:
--   The Flat Thickenings construction uses the flat of flat quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MemPowOfFlatQuotient.lean#L52-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MemPowOfFlatQuotient.lean#L52-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemPowOfFlatQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatThickenings

theorem GlobalTheory.FlatThickenings.flat_of_flat_quotient {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsNoetherianRing C] (σ : V →+* C)
    (h : ∀ e : ℕ, (Ideal.quotientMap ((IsLocalRing.maximalIdeal V ^ (e + 1)).map σ) σ
      (Ideal.le_comap_map (I := IsLocalRing.maximalIdeal V ^ (e + 1)))).Flat) : σ.Flat := by sorry

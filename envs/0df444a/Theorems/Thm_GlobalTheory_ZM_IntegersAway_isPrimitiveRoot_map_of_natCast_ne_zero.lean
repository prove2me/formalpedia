-- Prove2me | Theorems.Thm_GlobalTheory_ZM_IntegersAway_isPrimitiveRoot_map_of_natCast_ne_zero
-- name    : GlobalTheory.ZM.IntegersAway.isPrimitiveRoot_map_of_natCast_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:02:23.616902+00:00
-- url     : https://prove2.me/theorems/ec5a3f9b-a7d3-4d42-ae03-76cef1e27aef
-- title:
--   Integers Away: is Primitive Root map of nat Cast ne zero
-- statement:
--   The Integers Away construction uses the is Primitive Root map of nat Cast ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsPrimitiveRootMapOfNatCastNeZero.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsPrimitiveRootMapOfNatCastNeZero.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPrimitiveRootMapOfNatCastNeZero
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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.IntegersAway

theorem GlobalTheory.ZM.IntegersAway.isPrimitiveRoot_map_of_natCast_ne_zero {R K : Type} [CommRing R] [IsDomain R] [CharZero R] [Field K] {k : ℕ}
    (hk : 0 < k) {z : R} (hz : IsPrimitiveRoot z k) (β : R →+* K) (hβ : (k : K) ≠ 0) : IsPrimitiveRoot (β z) k := by sorry

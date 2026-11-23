-- Prove2me | Theorems.Thm_GlobalTheory_SegreCoord_secCoord_mk
-- name    : GlobalTheory.SegreCoord.secCoord_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:19.499934+00:00
-- url     : https://prove2.me/theorems/70a0ae49-169e-411c-bfbb-5b6ba43a2e53
-- title:
--   Segre Coord: sec Coord mk
-- statement:
--   The Segre Coord construction uses the sec Coord mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSegreCoordinates.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSegreCoordinates.lean#L71-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']

theorem GlobalTheory.SegreCoord.secCoord_mk {x : Sp T ⟶ X} {v : σ → T} (t : ∀ j : PUnit → M.ι, Γ(Sp T, (M.pull x).U j))
    (c : ∀ (y : Sp T), M.ι → (Sp T).presheaf.stalk y)
    (ht : ∀ j y, y ∈ (M.pull x).U j → gs (𝟙 _) y _ (t j) = c y (j PUnit.unit))
    (hu : ∀ y j, x y ∈ M.U j → IsUnit (c y j))
    (hc : ∀ y j j', x y ∈ M.U j → x y ∈ M.U j' → c y j = (gm x y _ (M.g j j')).val * c y j')
    (hv : ∀ y j i, x y ∈ M.U j → gs x y _ ((th i).f j) = ev y (v i) * c y j) : SecCoord M th x v := by sorry

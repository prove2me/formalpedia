-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_flat_fibres_dvr
-- name    : GlobalTheory.flat_of_flat_fibres_dvr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:52:04.588445+00:00
-- url     : https://prove2.me/theorems/97277bb6-fae1-4c24-a99f-cef25370c344
-- title:
--   Global Theory: flat of flat fibres dvr
-- statement:
--   The Global Theory construction uses the flat of flat fibres dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L182-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L182-L190

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

theorem GlobalTheory.flat_of_flat_fibres_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (X Y : Over (Sp T)) (φ : X ⟶ Y), Flat X.hom → Flat Y.hom →
      LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom →
      Flat ((Over.pullback (spMap (algebraMap T K))).map φ).left →
      Flat ((Over.pullback (spMap (IsLocalRing.residue T))).map φ).left → Flat φ.left := by sorry

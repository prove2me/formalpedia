-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlat_includeRight_bijective
-- name    : GlobalTheory.FibreFlat.includeRight_bijective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:09.976255+00:00
-- url     : https://prove2.me/theorems/39eda1ab-04de-41f4-9c87-97aa1e23606d
-- title:
--   Fibre Flat: include Right bijective
-- statement:
--   The Fibre Flat construction uses the include Right bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L19-L31

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
variable {T : Type*} (K : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
  [Algebra T K] [IsFractionRing T K]

theorem GlobalTheory.FibreFlat.includeRight_bijective {C : Type*} [CommRing C] [Algebra T C] {π : T} (hπ : Irreducible π)
    (hu : IsUnit (algebraMap T C π)) :
    Function.Bijective (Algebra.TensorProduct.includeRight : C →ₐ[T] K ⊗[T] C) := by sorry

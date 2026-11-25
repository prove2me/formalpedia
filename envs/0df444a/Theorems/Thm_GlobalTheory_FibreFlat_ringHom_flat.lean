-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlat_ringHom_flat
-- name    : GlobalTheory.FibreFlat.ringHom_flat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:55.187882+00:00
-- url     : https://prove2.me/theorems/89740af4-1040-437b-af96-0e536681a4a3
-- title:
--   Fibre Flat: ring Hom flat
-- statement:
--   The Fibre Flat construction uses the ring Hom flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L33-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L33-L76

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

theorem GlobalTheory.FibreFlat.ringHom_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra T A] [Algebra T B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat T B] (φ : A →ₐ[T] B)
    (hK : (Algebra.TensorProduct.map (AlgHom.id T K) φ : K ⊗[T] A →+* K ⊗[T] B).Flat)
    (hκ : (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
      ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat) : (φ : A →+* B).Flat := by sorry

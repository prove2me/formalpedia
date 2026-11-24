-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlat_FlatOver_tensor
-- name    : GlobalTheory.FibreFlat.FlatOver.tensor
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:58.582841+00:00
-- url     : https://prove2.me/theorems/4f628ebc-b879-4700-9672-5764608e020a
-- title:
--   Flat Over: tensor
-- statement:
--   The Flat Over construction uses the tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L122-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L122-L142

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

theorem GlobalTheory.FibreFlat.FlatOver.tensor {T L A B : Type} [CommRing T] [CommRing L] [CommRing A] [CommRing B]
    [Algebra T L] [Algebra T A] [Algebra T B] (φ : A →ₐ[T] B)
    (H : FlatOver (spMap (φ : A →+* B)) (spMap (algebraMap T A)) (spMap (algebraMap T L))) :
    (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat := by sorry

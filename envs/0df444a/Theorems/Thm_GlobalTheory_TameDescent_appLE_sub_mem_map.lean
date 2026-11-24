-- Prove2me | Theorems.Thm_GlobalTheory_TameDescent_appLE_sub_mem_map
-- name    : GlobalTheory.TameDescent.appLE_sub_mem_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:03:43.244562+00:00
-- url     : https://prove2.me/theorems/7bb4fafe-152d-4fc8-af28-a47089599812
-- title:
--   Tame Descent: app LE sub mem map
-- statement:
--   The Tame Descent construction uses the app LE sub mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsPullbackFlatOfTame.lean#L28-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsPullbackFlatOfTame.lean#L28-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemMapKerOfOneTmulEqZeroOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPullbackFlatOfTame
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameDescent

theorem GlobalTheory.TameDescent.appLE_sub_mem_map {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] (t : Y ⟶ Y) {U : X.Opens}
    {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U)
    (h : W ≤ t ⁻¹ᵁ W) {k : Type} [Field k] (a : Γ(X, U) →+* k)
    (ht : pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec) ≫ t =
      pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec)) (c : Γ(Y, W)) :
    (t.appLE W W h).hom c - c ∈ (RingHom.ker a).map (p.appLE U W e).hom := by sorry

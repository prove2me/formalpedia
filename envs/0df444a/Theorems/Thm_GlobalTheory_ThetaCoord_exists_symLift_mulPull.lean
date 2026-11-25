-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCoord_exists_symLift_mulPull
-- name    : GlobalTheory.ThetaCoord.exists_symLift_mulPull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:16:56.312149+00:00
-- url     : https://prove2.me/theorems/7341875e-6ad6-4ca5-a098-03fea50e837a
-- title:
--   Theta Coord: exists sym Lift mul Pull
-- statement:
--   The Theta Coord construction uses the exists sym Lift mul Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L213-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L213-L266

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}

theorem GlobalTheory.ThetaCoord.exists_symLift_mulPull (hA : IsAbelianScheme A) (hL : L.IsLB) {a b : ℤ} {r q q' : ℕ} (hq : q ∣ q')
    {β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ r).left] ![a, -b])} (hβ : β.IsGen)
    {y : T ⟶ A} (hy : y ^ q' = 1) {θ : ThetaGrp A L b T} (H : SymLift A L b q (y ^ r) θ) :
    ∃ θ' : ThetaGrp A L a T, SymLift A L a q' y θ' ∧
      ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
        tval θ' (lift π p).left z J = bval β (lift π p).left z J * tval θ (lift π (p ^ r)).left z J *
          (bval β (lift π ((π ≫ y) * p)).left z J)⁻¹ := by sorry

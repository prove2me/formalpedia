-- Prove2me | Theorems.Thm_GlobalTheory_PushInv_exists_secOn_pull_germ
-- name    : GlobalTheory.PushInv.exists_secOn_pull_germ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:28.281153+00:00
-- url     : https://prove2.me/theorems/29cad302-cfae-4f9c-91e8-25e89f0554f1
-- title:
--   Push Inv: exists sec On pull germ
-- statement:
--   The Push Inv construction uses the exists sec On pull germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L96-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L96-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.PushInv.exists_secOn_pull_germ {X' : Scheme.{0}} {F : X' ⟶ X} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) {W : X.Opens} {W' : X'.Opens} (hW : W' ≤ F ⁻¹ᵁ W)
    {θ : ∀ i, Γ(X, W ⊓ L.U i)} (hθ : θ ∈ secOn L W) :
    ∃ θ' ∈ secOn L' W', ∀ k x j, x ∈ W' → x ∈ L'.U k → F x ∈ L.U j →
      gs (𝟙 X') x _ (θ' k) = ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) := by sorry

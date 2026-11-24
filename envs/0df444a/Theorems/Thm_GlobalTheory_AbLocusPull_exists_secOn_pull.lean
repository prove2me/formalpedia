-- Prove2me | Theorems.Thm_GlobalTheory_AbLocusPull_exists_secOn_pull
-- name    : GlobalTheory.AbLocusPull.exists_secOn_pull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:09.034497+00:00
-- url     : https://prove2.me/theorems/54f8ddc9-b49a-4c5f-b1f2-07f0ff7317df
-- title:
--   Ab Locus Pull: exists sec On pull
-- statement:
--   The Ab Locus Pull construction uses the exists sec On pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProperRestrictPull.lean#L77-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProperRestrictPull.lean#L77-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
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
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.AbLocusPull.exists_secOn_pull {X' : Scheme.{0}} {F : X' ⟶ X} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hW : W' ≤ F ⁻¹ᵁ W) {θ : ∀ i, Γ(X, W ⊓ L.U i)}
    (hθ : θ ∈ secOn L W) :
    ∃ θ' ∈ secOn L' W', ∀ x ∈ W', ∀ j k, x ∈ L'.U k → F x ∈ X.basicOpen (θ j) → x ∈ X'.basicOpen (θ' k) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Cube_exists_normalised
-- name    : GlobalTheory.AbLaw.Cube.exists_normalised
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:39:57.889121+00:00
-- url     : https://prove2.me/theorems/c65d5b47-a1c8-4c38-bfc5-d55e2477d295
-- title:
--   Cube: exists normalised
-- statement:
--   The Cube construction uses the exists normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubicalOfNormalised.lean#L46-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubicalOfNormalised.lean#L46-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Cube
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}

theorem GlobalTheory.AbLaw.Cube.exists_normalised (hL : L.IsLB) (t : LB.Gen (Theta A L)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (Theta A L), t'.IsGen ∧ IsNormalised t' := by sorry

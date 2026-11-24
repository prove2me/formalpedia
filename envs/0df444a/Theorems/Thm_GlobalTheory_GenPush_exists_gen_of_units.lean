-- Prove2me | Theorems.Thm_GlobalTheory_GenPush_exists_gen_of_units
-- name    : GlobalTheory.GenPush.exists_gen_of_units
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:08:37.720799+00:00
-- url     : https://prove2.me/theorems/6941aa3d-0449-4bb3-9130-a8d479fbe746
-- title:
--   Gen Push: exists gen of units
-- statement:
--   The Gen Push construction uses the exists gen of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorIsoExtendFromOpenContainingCharts.lean#L61-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorIsoExtendFromOpenContainingCharts.lean#L61-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorIsoExtendFromOpenContainingCharts
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.GenPush
variable {X Y : Scheme.{0}}

theorem GlobalTheory.GenPush.exists_gen_of_units (c : Y ⟶ X) [IsOpenImmersion c] (N : LB X) (hN : ∀ a, N.U a ≤ c.opensRange)
    (V : N.ι → Y.Opens) (hV : ∀ a y, c y ∈ N.U a → y ∈ V a) (s : ∀ a, Γ(Y, V a)ˣ)
    (hs : ∀ (y : Y) a b, c y ∈ N.U a → c y ∈ N.U b →
      gm (𝟙 Y) y (V a) (s a) = gm c y (N.U a ⊓ N.U b) (N.g a b) * gm (𝟙 Y) y (V b) (s b)) :
    ∃ t : N.Gen, t.IsGen := by sorry

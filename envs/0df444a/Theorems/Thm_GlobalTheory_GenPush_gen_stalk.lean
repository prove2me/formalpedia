-- Prove2me | Theorems.Thm_GlobalTheory_GenPush_gen_stalk
-- name    : GlobalTheory.GenPush.gen_stalk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:38.419652+00:00
-- url     : https://prove2.me/theorems/ec0afd5d-7099-42ef-b474-974ea0e7a5bf
-- title:
--   Gen Push: gen stalk
-- statement:
--   The Gen Push construction uses the gen stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorIsoExtendFromOpenContainingCharts.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorIsoExtendFromOpenContainingCharts.lean#L92-L98

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

theorem GlobalTheory.GenPush.gen_stalk {N : LB Y} {t : N.Gen} (ht : t.IsGen) (y : Y) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j) :
    gm (𝟙 Y) y (N.U i) (t.s i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y (N.U j) (t.s j) := by sorry

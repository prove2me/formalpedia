-- Prove2me | Theorems.Thm_GlobalTheory_SqLB_gm_sq_g
-- name    : GlobalTheory.SqLB.gm_sq_g
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:49.968135+00:00
-- url     : https://prove2.me/theorems/0ebbf8ef-b998-4cf3-a192-ec8c086b87e8
-- title:
--   Sq LB: gm sq g
-- statement:
--   The Sq LB construction uses the gm sq g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIso.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIso.lean#L20-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSquareGeneratorThroughSquareIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SqLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem GlobalTheory.SqLB.gm_sq_g (f : Y ⟶ X) (y : Y) {j j' : L.ι} (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y ((sq L).U (fun _ => j) ⊓ (sq L).U (fun _ => j')) ((sq L).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ (2 : ℤ) := by sorry

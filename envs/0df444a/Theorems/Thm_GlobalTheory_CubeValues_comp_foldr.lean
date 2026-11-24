-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_comp_foldr
-- name    : GlobalTheory.CubeValues.comp_foldr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:11.807089+00:00
-- url     : https://prove2.me/theorems/0bfe9bd9-98e9-4d92-9238-70ebed97eebf
-- title:
--   Cube Values: comp foldr
-- statement:
--   The Cube Values construction uses the comp foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L113-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)

theorem GlobalTheory.CubeValues.comp_foldr {T T' : Over (Sp ℂ)} (p : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A)) (l : List (Fin n)) :
    p ≫ l.foldr (fun k acc => padd A (y k) acc) (pzero A T) = (l.map fun k => p ≫ y k).prod := by sorry

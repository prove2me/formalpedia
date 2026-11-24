-- Prove2me | Theorems.Thm_GlobalTheory_OpenSubgroupScheme_mem_range_iff_factors
-- name    : GlobalTheory.OpenSubgroupScheme.mem_range_iff_factors
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:39:59.889819+00:00
-- url     : https://prove2.me/theorems/70d5c5ca-dc93-43e5-8b38-568f26d6f62e
-- title:
--   Open Subgroup Scheme: mem range iff factors
-- statement:
--   The Open Subgroup Scheme construction uses the mem range iff factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean#L14-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
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
open GlobalTheory
open GlobalTheory.OpenSubgroupScheme
variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}

theorem GlobalTheory.OpenSubgroupScheme.mem_range_iff_factors (p : Ga ⟶ G) [IsOpenImmersion p.left] (x : 𝟙_ _ ⟶ G) :
    x.left (IsLocalRing.closedPoint K) ∈ Set.range p.left ↔ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = x := by sorry

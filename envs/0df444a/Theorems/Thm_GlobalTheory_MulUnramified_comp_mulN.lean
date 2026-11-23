-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_comp_mulN
-- name    : GlobalTheory.MulUnramified.comp_mulN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:28.083778+00:00
-- url     : https://prove2.me/theorems/5f2b9250-86ba-4b02-a50e-c6004d933c2b
-- title:
--   Mul Unramified: comp mul N
-- statement:
--   The Mul Unramified construction uses the comp mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L89-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
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
open GlobalTheory GlobalTheory.MulUnramified
variable {S : Scheme.{0}}

theorem GlobalTheory.MulUnramified.comp_mulN (G : Over S) [GrpObj G] {T : Over S} (x : T ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by sorry

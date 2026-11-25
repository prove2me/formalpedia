-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBundleSec_sec_unique
-- name    : GlobalTheory.ThetaBundleSec.sec_unique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:11.87786+00:00
-- url     : https://prove2.me/theorems/55baaad7-c98e-4d8f-86bb-c473ccb0e47c
-- title:
--   Theta Bundle Sec: sec unique
-- statement:
--   The Theta Bundle Sec construction uses the sec unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SectionsPowEqThetaLevelChar.lean#L90-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SectionsPowEqThetaLevelChar.lean#L90-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSec
open ThetaBundleSym
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem GlobalTheory.ThetaBundleSec.sec_unique [IsReduced A.left] [LocallyOfFiniteType A.hom] (u : HolUnif A L g) (n : ℕ)
    {θ : (Fin g → ℂ) → ℂ} {s s' : (lbPow L n).Sec} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ) : s = s' := by sorry

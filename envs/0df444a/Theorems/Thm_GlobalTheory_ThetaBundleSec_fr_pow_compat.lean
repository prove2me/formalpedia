-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBundleSec_fr_pow_compat
-- name    : GlobalTheory.ThetaBundleSec.fr_pow_compat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:47.4461+00:00
-- url     : https://prove2.me/theorems/5c3dad2f-2a16-451a-a6c0-268c415d1857
-- title:
--   Theta Bundle Sec: fr pow compat
-- statement:
--   The Theta Bundle Sec construction uses the fr pow compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SectionsPowEqThetaLevelChar.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SectionsPowEqThetaLevelChar.lean#L25-L42

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

theorem GlobalTheory.ThetaBundleSec.fr_pow_compat (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) (j j' : (lbPow L n).ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j') :
    u.fr (j PUnit.unit) z ^ n =
      valAt' (u.ex z).left ((lbPow L n).U j ⊓ (lbPow L n).U j') ((lbPow L n).g j j').val *
        u.fr (j' PUnit.unit) z ^ n := by sorry

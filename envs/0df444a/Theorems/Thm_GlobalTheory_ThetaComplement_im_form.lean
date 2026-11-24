-- Prove2me | Theorems.Thm_GlobalTheory_ThetaComplement_im_form
-- name    : GlobalTheory.ThetaComplement.im_form
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:24.706655+00:00
-- url     : https://prove2.me/theorems/2abf03f1-3720-4fb8-8c6a-3efcc752d39f
-- title:
--   Theta Complement: im form
-- statement:
--   The Theta Complement construction uses the im form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsComplementaryThetaOfLinearMap.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsComplementaryThetaOfLinearMap.lean#L45-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsComplementaryThetaOfLinearMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaComplement

theorem GlobalTheory.ThetaComplement.im_form {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hH : H.IsHermitian) (u v : Fin g → ℂ) :
    2 * I * ((u ⬝ᵥ H.mulVec (star v)).im : ℂ)
      = u ⬝ᵥ H.mulVec (star v) - v ⬝ᵥ H.mulVec (star u) := by sorry

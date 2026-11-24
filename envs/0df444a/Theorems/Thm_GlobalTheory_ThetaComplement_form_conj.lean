-- Prove2me | Theorems.Thm_GlobalTheory_ThetaComplement_form_conj
-- name    : GlobalTheory.ThetaComplement.form_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:07.707418+00:00
-- url     : https://prove2.me/theorems/d5498574-29cf-48df-a643-01cebedfe6d7
-- title:
--   Theta Complement: form conj
-- statement:
--   The Theta Complement construction uses the form conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsComplementaryThetaOfLinearMap.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsComplementaryThetaOfLinearMap.lean#L170-L175

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

theorem GlobalTheory.ThetaComplement.form_conj {g : ℕ} (H M : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    u ⬝ᵥ (Mᵀ * H * Mᵀᴴ).mulVec (star v) = (M *ᵥ u) ⬝ᵥ H.mulVec (star (M *ᵥ v)) := by sorry

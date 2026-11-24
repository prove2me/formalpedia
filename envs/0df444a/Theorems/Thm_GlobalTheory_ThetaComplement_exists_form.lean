-- Prove2me | Theorems.Thm_GlobalTheory_ThetaComplement_exists_form
-- name    : GlobalTheory.ThetaComplement.exists_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:22.40594+00:00
-- url     : https://prove2.me/theorems/e451d39e-cc39-4627-a2b8-e245d925e330
-- title:
--   Theta Complement: exists form
-- statement:
--   The Theta Complement construction uses the exists form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsComplementaryThetaOfLinearMap.lean#L53-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsComplementaryThetaOfLinearMap.lean#L53-L100

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

theorem GlobalTheory.ThetaComplement.exists_form {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ ∈ SiegelH (Fin g)) :
    ∃ H : Matrix (Fin g) (Fin g) ℂ, H.IsHermitian ∧ H.IsSymm ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) ∧
      ∀ n n' : Fin g → ℤ, H.mulVec (star (τ *ᵥ ofIntVec n + ofIntVec n'))
        = H.mulVec (τ *ᵥ ofIntVec n + ofIntVec n') - (2 * I) • ofIntVec n := by sorry

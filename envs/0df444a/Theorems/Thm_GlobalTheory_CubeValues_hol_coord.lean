-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_hol_coord
-- name    : GlobalTheory.CubeValues.hol_coord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:26.743832+00:00
-- url     : https://prove2.me/theorems/11cd3a11-39f0-4002-8735-4fac7791c291
-- title:
--   Cube Values: hol coord
-- statement:
--   The Cube Values construction uses the hol coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L151-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L151-L162

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

theorem GlobalTheory.CubeValues.hol_coord (a : Fin 3) (U : A.left.Opens) (f : Γ(A.left, U)) :
    IsOpen {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w : Fin 3 → Fin g → ℂ => valAt' (u.ex (w a)).left U f)
        {w | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} := by sorry

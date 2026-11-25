-- Prove2me | Theorems.Thm_GlobalTheory_T_tendsto_thH_pushZ_atTop_thH_dropF
-- name    : GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:17:00.316936+00:00
-- url     : https://prove2.me/theorems/10cb1c91-f571-4e2a-9c18-c490bc4fa295
-- title:
--   T: tendsto th H push Z at Top th H drop F
-- statement:
--   The T construction uses the tendsto th H push Z at Top th H drop F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHSiegelOperatorStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHSiegelOperatorStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ), IsSB φ → IsSB (dropF φ) ∧ ∀ Z ∈ Hn Ψ (N + 1), dropZ Ψ Z ∈ Hn Ψ N ∧ (∀ t : ℝ, 0 ≤ t → pushZ Ψ Z (Pi.single 0 1) t ∈ Hn Ψ (N + 1)) ∧ ∀ z z' : CM Ψ n (N + 1), Tendsto (fun t : ℝ => thH Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) z z') atTop (𝓝 (thH Ψ (dropF φ) (dropZ Ψ Z) (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))) := by sorry

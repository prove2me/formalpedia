-- Prove2me | Theorems.Thm_GlobalTheory_T_degenerationData_psi_quadratic_generators_linear
-- name    : GlobalTheory.T.degenerationData_psi_quadratic_generators_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:40.379017+00:00
-- url     : https://prove2.me/theorems/d62785ba-21f1-45af-bb87-3ed9aafed348
-- title:
--   T: degeneration Data psi quadratic generators linear
-- statement:
--   The T construction uses the degeneration Data psi quadratic generators linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataPsiQuadraticGeneratorsLinearStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataPsiQuadraticGeneratorsLinearStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinear
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem GlobalTheory.T.degenerationData_psi_quadratic_generators_linear : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X), N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧ ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧ (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n := by sorry

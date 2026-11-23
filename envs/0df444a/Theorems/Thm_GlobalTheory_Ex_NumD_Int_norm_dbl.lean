-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_dbl
-- name    : GlobalTheory.Ex.NumD.Int.norm_dbl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:21.164922+00:00
-- url     : https://prove2.me/theorems/cfe8d6dd-2105-467c-9a4c-71b606a28bc9
-- title:
--   Int: norm dbl
-- statement:
--   The Int construction uses the norm dbl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem GlobalTheory.Ex.NumD.Int.norm_dbl (h : N.Int q) (x : N.A) : ‖((dbl N.θ N.σ x : Cˣ) : C)‖ = 1 := by sorry

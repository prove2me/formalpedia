-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_pow_generators_eq_pow
-- name    : GlobalTheory.Ex.NumD.Int.norm_pow_generators_eq_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:36.034278+00:00
-- url     : https://prove2.me/theorems/e6c27907-d32d-4f41-92af-896ca7170942
-- title:
--   Int: norm pow generators eq pow
-- statement:
--   The Int construction uses the norm pow generators eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L28-L31

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

theorem GlobalTheory.Ex.NumD.Int.norm_pow_generators_eq_pow (h : N.Int q) (g : N.Gt) (k : ℕ) (χ : N.X) :
    ‖((g ^ k).s χ : C)‖ = ‖(g.s χ : C)‖ ^ k := by sorry

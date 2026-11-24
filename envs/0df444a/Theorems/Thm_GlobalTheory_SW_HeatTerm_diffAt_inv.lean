-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeatTerm_diffAt_inv
-- name    : GlobalTheory.SW.HeatTerm.diffAt_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:43.631814+00:00
-- url     : https://prove2.me/theorems/9cb334b1-e16c-4bdc-8557-48d057966fc7
-- title:
--   Heat Term: diff At inv
-- statement:
--   The Heat Term construction uses the diff At inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L21-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section

theorem GlobalTheory.SW.HeatTerm.diffAt_inv {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {N : ℕ}
    (A : X → Matrix (Fin N) (Fin N) ℂ) (x : X)
    (h : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x) (h0 : (A x).det ≠ 0) (i j : Fin N) :
    DifferentiableAt ℂ (fun y => (A y)⁻¹ i j) x := by sorry

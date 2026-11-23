-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_opU_mul
-- name    : GlobalTheory.ThetaInter.opU_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:45.232781+00:00
-- url     : https://prove2.me/theorems/ceda1751-02c1-47d2-9c8e-45d7af06e449
-- title:
--   Theta Inter: op U mul
-- statement:
--   The Theta Inter construction uses the op U mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L78-L80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}

theorem GlobalTheory.ThetaInter.opU_mul (x : V) (c : ℂ) (F : V → ℂ) (z : V) :
    opU H x (fun w => c * F w) z = c * opU H x F z := by sorry

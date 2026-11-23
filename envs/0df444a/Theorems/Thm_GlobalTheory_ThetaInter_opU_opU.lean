-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_opU_opU
-- name    : GlobalTheory.ThetaInter.opU_opU
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:02.552806+00:00
-- url     : https://prove2.me/theorems/56155c50-ada0-4342-811b-ed88767ebfad
-- title:
--   Theta Inter: op U op U
-- statement:
--   The Theta Inter construction uses the op U op U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L64-L69

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

theorem GlobalTheory.ThetaInter.opU_opU (hH : IsHerm H) (x y : V) (F : V → ℂ) (z : V) :
    opU H x (opU H y F) z = cexp (-(Real.pi * I * (altE H x y : ℂ))) * opU H (x + y) F z := by sorry

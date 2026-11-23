-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_opU_sum
-- name    : GlobalTheory.ThetaInter.opU_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:38.995809+00:00
-- url     : https://prove2.me/theorems/fcc82493-46c0-40b1-84b0-d6bd70f4563a
-- title:
--   Theta Inter: op U sum
-- statement:
--   The Theta Inter construction uses the op U sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L82-L84

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

theorem GlobalTheory.ThetaInter.opU_sum {ι : Type*} (s : Finset ι) (x : V) (F : ι → V → ℂ) (z : V) :
    opU H x (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, opU H x (F i) z := by sorry

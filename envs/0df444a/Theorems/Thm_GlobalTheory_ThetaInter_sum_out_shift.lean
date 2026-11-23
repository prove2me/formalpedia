-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_sum_out_shift
-- name    : GlobalTheory.ThetaInter.sum_out_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:43.745975+00:00
-- url     : https://prove2.me/theorems/14c32ce0-379d-4f10-b6c2-c49c2e5a83df
-- title:
--   Theta Inter: sum out shift
-- statement:
--   The Theta Inter construction uses the sum out shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L12-L21

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

theorem GlobalTheory.ThetaInter.sum_out_shift {G M : Type*} [AddCommGroup G] [AddCommMonoid M] (S : AddSubgroup G) [Fintype (G ⧸ S)]
    (f : G → M) (hf : ∀ a, ∀ s ∈ S, f (a + s) = f a) (g : G) :
    ∑ c : G ⧸ S, f (g + Quotient.out c) = ∑ c : G ⧸ S, f (Quotient.out c) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_alpha_opU_add
-- name    : GlobalTheory.ThetaInter.alpha_opU_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:07:02.649923+00:00
-- url     : https://prove2.me/theorems/8923677b-be60-433b-8b06-82cd28894192
-- title:
--   Theta Inter: alpha op U add
-- statement:
--   The Theta Inter construction uses the alpha op U add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L94-L102

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
variable {α : V → ℂ}

theorem GlobalTheory.ThetaInter.alpha_opU_add (hH : IsHerm H) {A : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) (F : V → ℂ) (z : V) :
    α (x + y) * opU H (x + y) F z = α x * (α y * opU H x (opU H y F) z) := by sorry

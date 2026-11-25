-- Prove2me | Theorems.Thm_GlobalTheory_iteratedDeriv_expG_line_eq_rightDeriv_pow
-- name    : GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:14:03.640413+00:00
-- url     : https://prove2.me/theorems/f97bdf7a-4632-4484-919a-1c9d756d04cf
-- title:
--   Global Theory: iterated Deriv exp G line eq right Deriv pow
-- statement:
--   The Global Theory construction uses the iterated Deriv exp G line eq right Deriv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivExpGLineEqRightDerivPow.lean#L13-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivExpGLineEqRightDerivPow.lean#L13-L44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_leftSmoothing_prodExp
-- name    : GlobalTheory.leftSmoothing_prodExp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:13.881842+00:00
-- url     : https://prove2.me/theorems/f25b10f4-be9c-44e7-b732-412264a52611
-- title:
--   Global Theory: left Smoothing prod Exp
-- statement:
--   The Global Theory construction uses the left Smoothing prod Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftSmoothingProdExpSmoothCommute.lean#L200-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftSmoothingProdExpSmoothCommute.lean#L200-L207

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommute
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
open GlobalTheory.LeftSmoothing

theorem GlobalTheory.leftSmoothing_prodExp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (n : ℕ) (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ), Continuous κ → HasCompactSupport κ → ∀ f : h.smoothFuns (F := ℂ), ∃ v : h.smoothFuns (F := ℂ), (∀ y, (v : G → ℂ) y = ∫ t, κ t * (f : G → ℂ) (h.prodExp X t * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T v : G → ℂ) y = ∫ t, κ t * (T f : G → ℂ) (h.prodExp X t * y) := by sorry

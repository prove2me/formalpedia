-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Bracket_hasDerivAt_exp
-- name    : GlobalTheory.SmoothForms.Bracket.hasDerivAt_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:41.315621+00:00
-- url     : https://prove2.me/theorems/95c9df2e-52c9-465c-b954-4211da6a4abe
-- title:
--   Bracket: has Deriv At exp
-- statement:
--   The Bracket construction uses the has Deriv At exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieCommutatorEqBracket.lean#L39-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Bracket
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

theorem GlobalTheory.SmoothForms.Bracket.hasDerivAt_exp (A : 𝔸) : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by sorry

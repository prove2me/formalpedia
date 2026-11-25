-- Prove2me | Theorems.Thm_GlobalTheory_dmin_rmul_near_one
-- name    : GlobalTheory.dmin_rmul_near_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:26.216578+00:00
-- url     : https://prove2.me/theorems/a3c89fd8-b49b-443d-b6af-8063e5364a2a
-- title:
--   Global Theory: dmin rmul near one
-- statement:
--   The Global Theory construction uses the dmin rmul near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L139-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L139-L183

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.dmin_rmul_near_one {r : ℕ} (X : Data E r) (x : Frame X.Ψ r)
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (A : Frame X.Ψ r) {δ : ℝ} (hδ : 0 ≤ δ) (hr : (r : ℝ) ^ 2 * δ ≤ 1 / 100)
    (hA : ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ δ) :
    rmul x A ∈ X.dom ∧ ∀ τ i, dmin X.Gm (rmul x A) τ i ≠ 0 ∧
      |Real.log ‖dmin X.Gm (rmul x A) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) := by sorry

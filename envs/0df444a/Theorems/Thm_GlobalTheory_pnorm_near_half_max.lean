-- Prove2me | Theorems.Thm_GlobalTheory_pnorm_near_half_max
-- name    : GlobalTheory.pnorm_near_half_max
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:18.623744+00:00
-- url     : https://prove2.me/theorems/53cd8060-e8d6-5b55-b4f2-116e3220af30
-- title:
--   Global Theory: pnorm near half max
-- statement:
--   The Global Theory construction uses the pnorm near half max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L225-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L225-L290

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

theorem GlobalTheory.pnorm_near_half_max {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : DifferentiableOn ℂ P X.dom) (S : ℝ)
    (hS : ∀ x ∈ X.dom, X.pnorm la P x ≤ S) (x : Frame X.Ψ r)
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hhalf : S / 2 ≤ X.pnorm la P x)
    (A : Frame X.Ψ r) (hA : ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|))) :
    rmul x A ∈ X.dom ∧ S / 4 ≤ X.pnorm la P (rmul x A) := by sorry

-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound
-- name    : OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T17:03:01.997433+00:00
-- url     : https://prove2.me/theorems/526061a2-2171-42b2-9f3d-6c5f1ca7b2f0
-- title:
--   An arithmetic lower bound for a selected interpolation minor
-- statement:
--   Let $m,K\in\mathbb N$ and $w_0,v_0,\theta,F,H,w_{\min}\in\mathbb R$. Let $p:\operatorname{Fin}(m)\to\mathbb Z$ and $q:\operatorname{Fin}(m)\to\mathbb N$ with $q_i\ge2$. Assume $K,w_0,v_0,\theta,H,w_{\min}>0$, $F\ge0$, and $w_{\min}\le\lceil\log q_i\rceil_+$ for every $i$. For a selection from the original row domain to the original column domain whose selected minor $M_{\mathrm{sel}}$ has nonzero determinant, put $\overline W=\operatorname{meanRowWeight}(K,v_0,\theta,q,H)$ and let $L$ be the source least-common-multiple constant. Then
--
--   $$-(1-\overline W)-\left(\frac{LFm}{v_0}+L\sum_i\frac1{\lceil\log q_i\rceil_+}+\frac{\theta}{w_{\min}}\right)\le\frac{\log\lVert\det M_{\mathrm{sel}}\rVert}{|\mathcal R|H}.$$
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L360-L393

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_clearing_bound

open OAI.PiExponent OAI.PiExponent.MatrixArithmetic
open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + θ / wmin) ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
  sorry

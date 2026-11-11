-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_B_2
-- name    : HZFixp.Main.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:35.855649+00:00
-- url     : https://prove2.me/theorems/331cfc2a-e025-489f-9347-f55687afceca
-- title:
--   Lemma B.2 — reciprocal gate: Q > 0.9/T, f(T, A) = J(A), f_y < −0.98
-- statement:
--   Let $\kappa>0$, $c\ge0$, $0<a\le b$, and let $[\ell,u]\subset(0,\infty)$ contain $[J(b),J(a)]$, $J(A)=\kappa/(A+c)+\beta$. Let $T$ be an integer with $T\ge\max\{1,20(u+|\beta|)\}$. Throughout the reciprocal gate's declared intervals ($A\in[a,b]$, $y\in[0.999T,1.001T]$), with $Q$ from (10) and $f=1/Q-y$:
--   $$Q(y,A) > \frac{0.9}{T},\qquad f(T,A)=J(A),\qquad \frac{\partial f}{\partial y}(y,A) < -0.98 .$$
--
--   This gives Lemma 3.7 for reciprocal gates with $m_0 = 0.98$.
--
--   Differences from the source:
--   - generalization: rational κ, c, β, a, b, ℓ, u → real parameters; reason: pointwise real analysis; rational values are a special case
--   - reading: reciprocal gate J(A) = κ/(A + c) + β (§3.3.2, Figure 6) → κ > 0 and c ≥ 0; reason: κ/R_T² and κ/(R_T D_T) are edge multiplicities and D_T/R_T an edge ratio, so κ > 0 and D_T = κ + R_T c > 0 for every admissible center T, which for arbitrarily large T (11) means c ≥ 0; every reciprocal gate of §3.3.1 has c ∈ {0, 1}
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 50 (PDF 52), Lemma B.2; construction p. 17 (PDF 19), step (1) and (10)

import Mathlib
import Definitions.Def_HZFixp_Main_Gates

namespace HZFixp.Main

/-- **Lemma B.2.** Throughout the reciprocal gate's declared intervals, `Q > 0.9/T`,
`f(T, A) = J(A)`, and `f_y < −0.98`. -/
theorem lemma_B_2 (κ c β a b ℓ u : ℝ) (T : ℕ) (hκ : 0 < κ) (hc : 0 ≤ c) (ha : 0 < a)
    (hab : a ≤ b) (hℓ : 0 < ℓ) (hℓJ : ℓ ≤ recJ κ c β b) (hJu : recJ κ c β a ≤ u) (hT₁ : 1 ≤ T)
    (hT : 20 * (u + |β|) ≤ (T : ℝ)) :
    ∀ A ∈ Set.Icc a b,
      recF κ c β T T A = recJ κ c β A ∧
      ∀ y ∈ Set.Icc (0.999 * (T : ℝ)) (1.001 * T),
        0.9 / (T : ℝ) < recQ κ c β T y A ∧
        deriv (fun t => recF κ c β T t A) y < -0.98 := by sorry

end HZFixp.Main

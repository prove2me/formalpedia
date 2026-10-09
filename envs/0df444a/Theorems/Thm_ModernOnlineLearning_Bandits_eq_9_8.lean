-- Prove2me | Theorems.Thm_ModernOnlineLearning_Bandits_eq_9_8
-- name    : ModernOnlineLearning.Bandits.eq_9_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:24.706746+00:00
-- url     : https://prove2.me/theorems/45048fbc-2fbc-42fa-b54c-b86cbc52bf0b
-- title:
--   Equation (9.8), p. 168 — Tsallis-INF regret controlled by square-root arm probabilities
-- statement:
--   Run Algorithm 9.6 against a fixed loss table with $0\le g_{t,i}\le L_\infty$, and let $k$ and $j$ be arms. If $x_{t,i}$ is the algorithm's probability of arm $i$ before the round-$t$ draw, then the expected mix-loss regret against arm $k$ obeys
--
--   $$\mathbb E\!\left[\sum_{t=1}^{T}\langle g_t,x_t-e_k\rangle\right]\le L_\infty\sum_{t=1}^{T}\left(4\sqrt t-4\sqrt{t-1}+\frac{12}{\sqrt t}\right)\sum_{i\ne j}\mathbb E[\sqrt{x_{t,i}}]\le L_\infty\sum_{t=1}^{T}\frac{16}{\sqrt t}\sum_{i\ne j}\mathbb E[\sqrt{x_{t,i}}].$$
--
--   This estimate is the chapter's direct input to both parts of Theorem 9.17.
--
--   **Formalization Note** The expression at $t=1$ uses $\sqrt{t-1}=0$. The source page has $4\sqrt t-4\sqrt{t-1}$; the chunk planning brief accidentally transcribed reciprocals here. Expectations use the finite conditional law of Algorithm 9.6.
-- source:
--   Orabona, arXiv:1912.13213v10, Eq. (9.8), p. 168

import Definitions.Def_ModernOnlineLearning_Bandits_Tsallis
set_option autoImplicit false
noncomputable section

namespace ModernOnlineLearning.Bandits

/-- Orabona, display (9.8), p. 168. The first coefficient is read from the
    rendered page as `4√t − 4√(t−1) + 12/√t`. -/
theorem eq_9_8 {T d : ℕ} (hd : 0 < d) (L : ℝ) (hL : 0 < L)
    (anchor : Fin d) (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ)
    (hBound : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ g t i ∧ g t i ≤ L)
    (hRun : IsTsallisRun L g x) (k j : Fin d) :
    expectedMixRegret anchor g x k ≤
      L * ∑ t ∈ Finset.Icc 1 T,
        (4 * Real.sqrt (t : ℝ) - 4 * Real.sqrt ((t : ℝ) - 1) +
          12 / Real.sqrt (t : ℝ)) *
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≠ j),
            expectedSqrtProbability anchor x t i
    ∧
    expectedMixRegret anchor g x k ≤
      L * ∑ t ∈ Finset.Icc 1 T,
        (16 / Real.sqrt (t : ℝ)) *
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≠ j),
            expectedSqrtProbability anchor x t i := by sorry

end ModernOnlineLearning.Bandits

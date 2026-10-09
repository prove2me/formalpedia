-- Prove2me | Theorems.Thm_ModernOnlineLearning_ToX_eg_regret_6_6
-- name    : ModernOnlineLearning.ToX.eg_regret_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:47.690598+00:00
-- url     : https://prove2.me/theorems/f021d390-5c26-4deb-9176-bee4c1701942
-- title:
--   §6.6, p. 81 — Exponentiated Gradient regret on the simplex
-- statement:
--   Let $d,T\ge1$ and $\eta>0$. Run Exponentiated Gradient from the uniform point on $\Delta^{d-1}$ against losses $\ell_t$, choosing a subgradient $g_t$ at each prediction $x_t$. Then for every fixed $u\in\Delta^{d-1}$,
--
--   $$
--   \sum_{t=1}^T\bigl(\ell_t(x_t)-\ell_t(u)\bigr)
--   \le\frac{\ln d}{\eta}+\frac\eta2\sum_{t=1}^T\|g_t\|_\infty^2.
--   $$
--
--   This is the regret estimate used with Theorem 16.4 to obtain the finite-class bound in Corollary 16.7.
--
--   **Formalization Note** Losses are represented by real-valued functions and the chosen subgradient satisfies the subgradient inequality for every comparator in the simplex. This records exactly the part of the book's extended-valued subgradient condition used by the regret estimate. The infinity norm is the maximum coordinate absolute value. The run predicate explicitly fixes the uniform initial point and the update rule of Algorithm 6.2.
-- source:
--   Orabona, arXiv:1912.13213v10, §6.6, p. 81, first display after Lemma 6.33; Algorithm 6.2, p. 80

import Mathlib
import Definitions.Def_ModernOnlineLearning_ToX_Algorithms

namespace ModernOnlineLearning.ToX

/-- The unnumbered EG regret display of §6.6, p. 81.
`IsEGRun` is Algorithm 6.2, p. 80; each `g t` is a subgradient of
the round's loss at `x t`. -/
theorem eg_regret_6_6 {d T : ℕ} [NeZero d] (hT : 1 ≤ T)
    (η : ℝ) (g x : ℕ → Fin d → ℝ)
    (loss : ℕ → (Fin d → ℝ) → ℝ)
    (hRun : IsEGRun T η g x)
    (hsub : ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ simplex d,
      loss t (x t) + pairing (g t) (y - x t) ≤ loss t y) :
    ∀ u ∈ simplex d,
      (∑ t ∈ Finset.Icc 1 T, (loss t (x t) - loss t u)) ≤
        Real.log (d : ℝ) / η +
          η / 2 * ∑ t ∈ Finset.Icc 1 T,
            (Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin d => |g t i|)) ^ 2 := by sorry

end ModernOnlineLearning.ToX

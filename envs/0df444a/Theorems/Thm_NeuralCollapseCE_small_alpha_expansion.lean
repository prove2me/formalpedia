-- Prove2me | Theorems.Thm_NeuralCollapseCE_small_alpha_expansion
-- name    : NeuralCollapseCE.small_alpha_expansion
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:13:19.548252+00:00
-- url     : https://prove2.me/theorems/ee340138-a143-4513-86e0-3a81eb46dbeb
-- title:
--   Proposition 6 (as proved): second-order expansion as $\alpha\to0$
-- statement:
--   Let $u_1,\dots,u_n$ be unit vectors in $\mathbb{R}^d$ and $U=\sum_{j}u_j$. As $\alpha\to0$,
--
--   $$\sum_{i=1}^n\log\Big(\sum_{j=1}^ne^{\alpha\langle u_i,u_j\rangle}\Big)=n\log n+\frac{\alpha}{n}\|U\|^2+\frac{\alpha^2}{2n}\sum_{i,j=1}^n\langle u_i,u_j\rangle^2-\frac{\alpha^2}{2n^2}\sum_{i=1}^n\langle u_i,U\rangle^2+\mathcal O(\alpha^3).$$
--
--   The leading terms form an effective energy close to the frame potential of Benedetto and Fickus, with a strong incentive for $U=0$.
--
--   **Formalization Note** The printed Proposition 6 has $\frac{\alpha^2}{2n}$ in front of the last sum; its proof (Section 6) produces $\frac{\alpha^2}{2n^2}$, which is the correct coefficient (for $n=2$, $u_1=u_2$ the printed version leaves an error of order $\alpha^2$). The statement is the one the proof establishes. $\mathcal O(\alpha^3)$ is Landau's big-O as $\alpha\to0$ for the fixed configuration.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 1.4, Proposition 6, p. 4; proof in Section 6, p. 15 (coefficient of the last term as in the proof)

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem small_alpha_expansion {n d : ℕ} (u : Fin n → Vec d) (hu : IsUnitConfig u) :
    (fun α : ℝ =>
      ∑ i, Real.log (∑ j, Real.exp (α * inner ℝ (u i) (u j))) -
        ((n : ℝ) * Real.log n + α / n * ‖∑ i, u i‖ ^ 2 +
          α ^ 2 / (2 * n) * ∑ i, ∑ j, (inner ℝ (u i) (u j)) ^ 2 -
          α ^ 2 / (2 * (n : ℝ) ^ 2) * ∑ i, (inner ℝ (u i) (∑ j, u j)) ^ 2))
      =O[𝓝 0] (fun α : ℝ => α ^ 3) := by sorry

end NeuralCollapseCE

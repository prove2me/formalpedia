-- Prove2me | Theorems.Thm_NeuralCollapseCE_sym_loss_lower_bound
-- name    : NeuralCollapseCE.sym_loss_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:09:53.052104+00:00
-- url     : https://prove2.me/theorems/28416293-fc53-4830-998b-f18b5a80b2cf
-- title:
--   Theorem 2, eq. (7): lower bound for the symmetric loss
-- statement:
--   Let $n\ge2$, $\alpha>0$, and let $u_1,\dots,u_n\in\mathbb{R}^d$ be unit vectors. Then
--
--   $$\mathcal{L}_\alpha(u)\ \ge\ n\log\Big(1+(n-1)\,e^{-\frac{n\alpha}{n-1}}\Big).$$
--
--   This is the lower bound (7) obtained in the proof of Theorem 2 by two applications of Jensen's inequality. It is attained exactly by the simplex equiangular tight frames, which gives the value of the minimum in Theorem 2.
--
--   **Formalization Note** The bound holds for every dimension $d$; the hypothesis $d\ge n-1$ of Theorem 2 is used only for attainment and is not assumed.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 2 (proof of Theorem 2), eq. (7), p. 6

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem sym_loss_lower_bound {n d : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α)
    (u : Fin n → Vec d) (hu : IsUnitConfig u) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp (-((n : ℝ) * α / ((n : ℝ) - 1)))) ≤
      symLoss α u := by sorry

end NeuralCollapseCE

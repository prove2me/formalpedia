-- Prove2me | Theorems.Thm_LSWCuttingPlane_ChasingZero_exp_taylor_bound
-- name    : LSWCuttingPlane.ChasingZero.exp_taylor_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:35.457157+00:00
-- url     : https://prove2.me/theorems/d672b7d4-d9c7-4478-a67c-5507cc2f80dc
-- title:
--   Proof of Theorem 34, p. 43 — eˣ ≤ 1 + x + (x²/2)e^{|x|}, hence e^{αx+αδ} ≤ e^{αx} + αδe^{αx} + ½α²δ²e^{αx+|α|c} for |δ| ≤ c
-- statement:
--   For every real number $x$,
--   $$e^x\le 1+x+\frac{x^2}{2}e^{|x|},$$
--   and consequently, for all real $c$, $\delta$, $x$, $\alpha$ with $|\delta|\le c$,
--   $$e^{\alpha x+\alpha\delta}\le e^{\alpha x}+\alpha\delta e^{\alpha x}+\frac12\alpha^2\delta^2e^{\alpha x+|\alpha|c}.$$
--
--   This second-order bound on the exponential is the first step of the proof of Theorem 34: applied coordinatewise, it controls the expected growth of the exponential potential $\Phi$ under a random mean-zero move.
--
--   **Formalization Note** The two parts are stated as a conjunction; the second quantifies over all real $c$ (the hypothesis $|\delta|\le c$ forces $c\ge 0$).
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 43, proof of Theorem 34, first display

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting

namespace LSWCuttingPlane.ChasingZero

/-- Proof of Theorem 34, p. 43, first display: `e^x ≤ 1 + x + (x²/2) e^{|x|}` for all real `x`,
and therefore `e^{αx+αδ} ≤ e^{αx} + αδ e^{αx} + ½ α² δ² e^{αx + |α| c}` whenever `|δ| ≤ c`. -/
theorem exp_taylor_bound :
    (∀ x : ℝ, Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp |x|) ∧
    (∀ c δ x α : ℝ, |δ| ≤ c →
      Real.exp (α * x + α * δ) ≤
        Real.exp (α * x) + α * δ * Real.exp (α * x)
          + 1 / 2 * α ^ 2 * δ ^ 2 * Real.exp (α * x + |α| * c)) := by sorry

end LSWCuttingPlane.ChasingZero

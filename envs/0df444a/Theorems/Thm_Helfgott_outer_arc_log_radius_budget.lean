-- Prove2me | Theorems.Thm_Helfgott_outer_arc_log_radius_budget
-- name    : Helfgott.outer_arc_log_radius_budget
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T17:18:53.073923+00:00
-- url     : https://prove2.me/theorems/d06c499c-47ab-450e-86a9-67458bd13d51
-- title:
--   A one-percent budget for the far outer Goldbach arcs at large scale
-- statement:
--   Let $x\ge49e^{3000}$, put $L=\log(x/49)$ and $r=\lceil L^{10}\rceil$, and use Helfgott's actual parity-dependent major arcs $\mathfrak M_{8,r}(x)$. For the actual smoothings $\eta_+$ and $\eta_*$,
--
--   $$\int_{\mathfrak M_{8,r}(x)^c}|S_{\eta_+}(x,\alpha)|^2|S_{\eta_*}(x,\alpha)|\,d\alpha
--   \le\frac1{100}\,\frac{x^2}{49}.$$
--
--   The integral uses normalized Haar measure on the circle. This bounds the far outer region with all numerical conditions discharged. The intermediate region between the fixed Goldbach major arcs and the growing radius $r$ remains outside this theorem's scope.
-- source:
--   Derived from the proved Helfgott.etaStar_tao_minorArc_radius and Helfgott.etaPlus_square_energy_le_64, with exact polynomial-exponential comparisons and Parseval. The Parseval infrastructure is adapted from accepted submission 8d315dcd-ee20-42e9-8a45-3d031aab3f66 by Ethan Cheung Wang.

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.Algebra.Order.Floor.Ring
open MeasureTheory Helfgott

theorem Helfgott.outer_arc_log_radius_budget (x : ℝ) (hx : 49*Real.exp 3000 ≤ x) :
    let r := ⌈(Real.log (x/49))^10⌉₊
    (∫ α in (majorArcs 8 r x)ᶜ,
      ‖coordinatedExpSum etaPlus x α‖^2*‖coordinatedExpSum etaStar x α‖
        ∂AddCircle.haarAddCircle) ≤ (1/100:ℝ)*(x^2/49) := by sorry

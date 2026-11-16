-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_reusable_decisions_centered_releases
-- name    : MinimaxInterventions1429.Separable.Supplement.reusable_decisions_centered_releases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:19:20.061299+00:00
-- url     : https://prove2.me/theorems/736a42e3-f0c2-485c-a594-8123b83b22b8
-- title:
--   Theorem 6.4 — Reusable decisions are centered releases
-- statement:
--   Fix any public group design and family $L_\theta(y)=\tfrac14\mathbf1+\tfrac12(Ay)\mathbf1_2^\top+\theta[0,Aw]$, including duplicate groups, singleton groups and $\theta=0$. Let $\Lambda=\theta\operatorname{osc}(Aw)$. For all $\varepsilon\ge0$ and $\delta,\beta\in[0,1)$,
--   $$\min\{\Lambda/8,\mathrm{err}_A/6\}\le\mathrm{dec}_A\le\min\{\Lambda,\mathrm{err}_A\}.$$
--   Here $\mathrm{err}_A$ is the infimal private centered release error of $Ay$, measured modulo a scalar, and $\mathrm{dec}_A$ uses one simultaneous success event on bounded separable queries. Privacy holds at all binary databases. This characterizes the cost that separable reusable decisions expose.
--
--   Differences from the source:
--   - encoding: centered error inf_lambda ||v-Ay-lambda 1||_infinity → half the finite error oscillation; reason: the attained scalar midrange gives exactly the same centered error
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 6.4, printed p.20 (PDF p.22)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Groups
set_option autoImplicit false
universe u_reusable_decisions_centered_releases

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem reusable_decisions_centered_releases
    {N m : ℕ} [NeZero m] (hm : 2 ≤ m) (d : GroupDesign N m)
    (ε δ β : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ ∧ δ < 1) (hβ : 0 ≤ β ∧ β < 1) :
    min (d.lambda / 8) (centeredReleaseError d ε δ β / 6) ≤
      decisionError replacement d.table {B | Allowed B} ε δ β ∧
    decisionError replacement d.table {B | Allowed B} ε δ β ≤
      min d.lambda (centeredReleaseError d ε δ β) := by sorry

end MinimaxInterventions1429.Separable.Supplement

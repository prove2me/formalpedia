-- Prove2me | Theorems.Thm_FrieszDUE_PIE_failure_set_pos_measure_46
-- name    : FrieszDUE.PIE.failure_set_pos_measure_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:19:42.192422+00:00
-- url     : https://prove2.me/theorems/fa761dfa-6783-4369-a507-0c0a2a11fe3a
-- title:
--   (44)–(46), pp. 187–188 — if S_p has positive measure, so does S_p(ε, δ) for some ε, δ > 0
-- statement:
--   In the setting of the PIE model, let $T>0$, let $h^*\in\Lambda$, suppose every cost $C_p(\cdot,h^*)$ is square-integrable on $[0,T]$, write $\mu^*_{kl}=\mu_{kl}(h^*)$, and fix a path $p\in P_{kl}$. If the set
--
--   $$S_p=\{t\in[0,T]: h^*_p(t)>0,\ C_p(t,h^*)-\mu^*_{kl}>0\}\qquad(44)$$
--
--   has positive measure, then there exist $\varepsilon>0$ and $\delta>0$ such that
--
--   $$S_p(\varepsilon,\delta)=\{t\in S_p: C_p(t,h^*)-\mu^*_{kl}>2\varepsilon,\ h^*_p(t)>\delta\}\qquad(45),(46)$$
--
--   has positive measure.
--
--   This is the first step of the contradiction argument in the sufficiency half of Theorem 2: a failure of (16) on a set of positive measure leaves a set of positive measure with a uniform cost gap $2\varepsilon$ and a uniform flow $\delta$ that can be shifted.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), pp. 187–188, proof of Theorem 2 part ii, (44)–(46)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Proof of Theorem 2 part ii, (44)–(46), pp. 187–188. -/
theorem failure_set_pos_measure_46 {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (hT : 0 < T) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ) (hhs : hs ∈ Lambda T od Q)
    (hC_L2 : ∀ p, MemLp (fun t => C p t hs) 2 (ν T)) (p : P)
    (hSp : 0 < ν T {t | 0 < hs p t ∧ muOD T od C hs (od p) < C p t hs}) :
    ∃ ε > 0, ∃ δ > 0, 0 < ν T {t | 0 < hs p t ∧ muOD T od C hs (od p) + 2 * ε < C p t hs ∧
      δ < hs p t} := by sorry

end FrieszDUE.PIE

-- Prove2me | Theorems.Thm_KServer_workFnU_step_approx
-- name    : KServer.workFnU_step_approx
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:00:25.660017+00:00
-- url     : https://prove2.me/theorems/e9d4d37f-645b-4c7d-8d6d-a8ab5f71d2e6
-- title:
--   One step of the unordered work-function recurrence: lower half
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$, a request sequence $\sigma$, one further request $r$ and a target configuration $Z$; write $\widehat w_\sigma$ for the unordered work function after $\sigma$.
--
--   **Statement.** For every $\varepsilon>0$ there is a configuration $Y$ covering $r$ with
--   $$\widehat w_\sigma(Y)+d(Y,Z)\;\le\;\widehat w_{\sigma r}(Z)+\varepsilon .$$
--
--   The $\varepsilon$ is necessary: on a general metric space the infimum over configurations covering $r$ need not be attained. Choosing $\varepsilon_t=2^{-t}$ at step $t$ bounds the accumulated slack by $1$, which the additive constant of competitiveness absorbs.
--
--   **Role.** Together with its companion this is the one-step recurrence of the *unordered* work function,
--   $$\widehat w_{\sigma r}(Z)\;=\;\inf\bigl\{\,\widehat w_\sigma(Y)+d(Y,Z)\ :\ r\in Y\,\bigr\},$$
--   which is what the Work Function Algorithm is defined by and what the Extended Cost Lemma for `workFnU` runs on. On a space of $k+1$ points, where a configuration of distinct points is determined by the point it leaves uncovered, this recurrence is exactly the avoidance recurrence
--   $$\widehat w_t(h)=\min_{g\neq r_t}\bigl\{\widehat w_{t-1}(g)+d(g,h)\bigr\}$$
--   on the $k+1$ holes.
--
--   **Formalization Note** The movement cost appearing here is the ordinary **labelled** one, $\sum_i d(Y_i,Z_i)$, even though both work functions are unordered. That is not an oversight: a relabelling may be transferred from one argument of `moveCost` to the other, $d(Y\circ\pi^{-1},Z)=d(Y,Z\circ\pi)$, and it is this that lets the minimum over relabellings pass through the recurrence. It is also what allows the Work Function Algorithm to keep paying the labelled cost of its own moves while its potential is measured by the unordered work function, with no minimum-cost-matching machinery anywhere.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, equation (4), and Section 3.4 (the Work Function Algorithm and its characteristic equation (7)); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_step_approx (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Z : Config k M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : Config k M, (∃ i, Y i = r) ∧
      workFnU C₀ σ Y + moveCost Y Z ≤ workFnU C₀ (σ ++ [r]) Z + ε := by sorry

end KServer

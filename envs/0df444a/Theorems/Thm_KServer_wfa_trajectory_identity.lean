-- Prove2me | Theorems.Thm_KServer_wfa_trajectory_identity
-- name    : KServer.wfa_trajectory_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T21:36:52.569174+00:00
-- url     : https://prove2.me/theorems/76c7b223-8560-4811-bf25-e8df1f02b53a
-- title:
--   The trajectory identity for the Work Function Algorithm
-- statement:
--   Let $\mathrm{WFA}$ run from the initial configuration $C_0$ on the request sequence $\sigma = r_1 \dots r_n$, and write $A_t$ for its configuration after $t$ requests and $w_t = w_{C_0, r_1 \dots r_t}$ for the work function of the first $t$ requests. Then
--
--   $$\mathrm{cost}(\mathrm{WFA}, \sigma) \;+\; w_n(A_n) \;=\; \sum_{t=0}^{n-1} \bigl( w_{t+1}(A_t) - w_t(A_t) \bigr).$$
--
--   The cost of the Work Function Algorithm, plus the work function of the whole sequence evaluated at the algorithm's own final configuration, is *exactly* the sum of the increments of the work function measured **at the algorithm's own configuration** immediately before each request.
--
--   ## Why this is the right form
--
--   The standard potential-function analyses of $\mathrm{WFA}$ --- Chrobak and Larmore's, Bein--Chrobak--Larmore's, Koutsoupias's, and the Coester--Koutsoupias potential method --- all begin from a bound of the shape
--
--   $$\mathrm{cost}(\mathrm{WFA}, \sigma) + \mathrm{OPT}(\sigma) \;\le\; \sum_{t} u_t, \qquad u_t \ge \max_X \bigl( w_{t+1}(X) - w_t(X) \bigr),$$
--
--   where the budget $u_t$ dominates the *extended cost*, the largest increase of the work function over **all** configurations. That form is convenient, because the right-hand side then depends on the work function alone and not on the algorithm, which is what lets a potential $\Phi(w)$ certify competitiveness. But it is not tight: it is a weakening of the identity above, obtained by replacing the increment at the single configuration $A_t$ by the maximum over all $X$, and then bounding $w_n(A_n) \ge \mathrm{OPT}(\sigma)$.
--
--   The identity records what the telescoping argument actually proves before either weakening is applied. It is an equality, so nothing is lost; every bound of the displayed shape --- and any sharper one that only controls the increments along the trajectory --- follows from it by monotonicity of the sum.
--
--   ## The proof
--
--   Two facts drive it.
--
--   The first is the *step identity*: after the request $r_{t+1}$,
--
--   $$w_{t+1}(A_t) \;=\; w_{t+1}(A_{t+1}) + d(A_t, A_{t+1}).$$
--
--   This says that the move $\mathrm{WFA}$ makes on the request $r_{t+1}$ costs exactly the difference between the new work function at the old configuration and at the new one --- the algorithm is, in this sense, *lazy with respect to the new work function*. The inequality $\le$ is $1$-Lipschitzness of $w_{t+1}$; the inequality $\ge$ combines the recurrence for the work function (some server can be sent to $r_{t+1}$ from $A_t$ realising $w_{t+1}(A_t)$) with the defining minimality of the $\mathrm{WFA}$ step.
--
--   The second is telescoping. Writing $f_t = w_t(A_t)$ and $g_t = w_{t+1}(A_t) - w_t(A_t)$ for the increment along the trajectory, the step identity says exactly
--
--   $$d(A_t, A_{t+1}) \;=\; g_t + \bigl(f_t - f_{t+1}\bigr),$$
--
--   and summing over $t < n$ gives $\mathrm{cost} = \sum_t g_t + f_0 - f_n$. Finally $f_0 = w_0(A_0) = d(C_0, C_0) = 0$, which yields the identity.
--
--   ## Note on the formal statement
--
--   The work function here is the one of the ambient development, defined through `moveCost`, the sum of the distances travelled by the individually labelled servers; `WFA` is the algorithm that after each request moves to a configuration covering it minimizing movement plus the new work function, with ties broken by a fixed choice. The identity is insensitive to the tie-breaking rule: the step identity holds for *any* minimizer, so the theorem is proved for the algorithm as defined, whatever the choice function returns.
-- source:
--   The telescoping core of the standard analysis of the Work Function Algorithm; the customary weakened form is Lemma 2 of W. Bein, M. Chrobak, L. Larmore, 'The 3-server problem in the plane', Theoretical Computer Science 289 (2002), and the same step appears in E. Koutsoupias, 'The k-server problem', Computer Science Review 3 (2009), Section 3, and in C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021. Stated here as the exact identity, before the extended-cost weakening.

import Mathlib
import Definitions.Def_KServer_work_function

namespace KServer

theorem wfa_trajectory_identity (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (σ : List M) :
    (WFA hk C₀).cost σ + workFunction C₀ σ ((WFA hk C₀).conf σ)
      = ∑ t ∈ Finset.range σ.length,
          (workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
            - workFunction C₀ (σ.take t) ((WFA hk C₀).conf (σ.take t))) := by sorry

end KServer

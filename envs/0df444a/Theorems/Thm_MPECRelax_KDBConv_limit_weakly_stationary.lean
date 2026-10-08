-- Prove2me | Theorems.Thm_MPECRelax_KDBConv_limit_weakly_stationary
-- name    : MPECRelax.KDBConv.limit_weakly_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:38.783296+00:00
-- url     : https://prove2.me/theorems/e411ac1f-b991-4e8e-85f7-a414f9a87913
-- title:
--   Proof of Theorem 3.5, pp. 16–17 — the limit of KKT points of R^KDB(t_k) is weakly stationary
-- statement:
--   Let the data of the MPEC (1) be continuously differentiable, let $\{t_k\}\downarrow 0$, and let $x^k$ be a stationary point of the relaxed program $R^{KDB}(t_k)$ for every $k\in\mathbb N$. If $x^k\to x^*$ and MPEC-CPLD holds at $x^*$, then $x^*$ is feasible for the MPEC (1) and weakly stationary: there are $\lambda\in\mathbb R^m$, $\mu\in\mathbb R^p$, $\gamma,\nu\in\mathbb R^l$ with
--   $$\nabla f(x^*)+\sum_{i=1}^m\lambda_i\nabla g_i(x^*)+\sum_{i=1}^p\mu_i\nabla h_i(x^*)-\sum_{i=1}^l\gamma_i\nabla G_i(x^*)-\sum_{i=1}^l\nu_i\nabla H_i(x^*)=0,$$
--   $\lambda\ge 0$, $\lambda_ig_i(x^*)=0$, $\gamma_i=0$ for $i\in I_{+0}$ and $\nu_i=0$ for $i\in I_{0+}$.
--
--   This is the first half of Theorem 3.5; the remaining work is the sign analysis on the biactive set $I_{00}$ that upgrades weak to M-stationarity.
--
--   **Formalization Note** "Stationary point" means feasible with KKT multipliers (p. 5). "$\{t_k\}\downarrow 0$" is $t_k>0$, $t$ nonincreasing, $t_k\to0$. The standard constraints $g$, $h$, which the paper's proof skips, are part of the statement. Weak stationarity follows Definition 2.3(a) with its two misprints corrected (see the definitions file), and includes feasibility of $x^*$, which the hypotheses imply.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 16–17, proof of Theorem 3.5 ("This means that x* is at least weakly stationary")

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace MPECRelax.KDBConv

/-- Proof of Theorem 3.5, pp. 16–17: under the hypotheses of Theorem 3.5 the limit `xs`
is (feasible and) weakly stationary for the MPEC (1). -/
theorem limit_weakly_stationary {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → MPECRelax.ScholtesConv.E n) (hx : ∀ k, (P.RKDB (t k)).IsKKTPoint (x k))
    (xs : MPECRelax.ScholtesConv.E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_CPLD xs) :
    P.IsWeaklyStationary xs := by sorry

end MPECRelax.KDBConv

-- Prove2me | Theorems.Thm_MPECRelax_KDBConv_theorem_3_5
-- name    : MPECRelax.KDBConv.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:55.978614+00:00
-- url     : https://prove2.me/theorems/b550b50f-f931-458d-a3a6-db3aab513540
-- title:
--   Theorem 3.5 — limits of KKT points of the Kadrani et al. relaxation are M-stationary under MPEC-CPLD
-- statement:
--   Consider the MPEC (1) with continuously differentiable data $f,g_i,h_i,G_i,H_i:\mathbb R^n\to\mathbb R$, and for $t>0$ the relaxed program of Kadrani, Dussault and Benchakroun
--   $$R^{KDB}(t):\quad \min f(x)\ \text{ s.t. }\ g(x)\le 0,\ h(x)=0,\ G_i(x)\ge -t,\ H_i(x)\ge -t,\ (G_i(x)-t)(H_i(x)-t)\le 0\ \ (i=1,\dots,l).$$
--
--   **Theorem 3.5.** Let $\{t_k\}\downarrow 0$ and assume that $x^k$ is a stationary point of $R^{KDB}(t_k)$ for all $k\in\mathbb N$. Moreover, suppose that $x^k\to x^*$ such that MPEC-CPLD holds at $x^*$. Then $x^*$ is an M-stationary point of (1):
--   $x^*$ is feasible for (1), and there are multipliers $\lambda\in\mathbb R^m$, $\mu\in\mathbb R^p$, $\gamma,\nu\in\mathbb R^l$ with
--   $$\nabla f(x^*)+\sum_{i=1}^m\lambda_i\nabla g_i(x^*)+\sum_{i=1}^p\mu_i\nabla h_i(x^*)-\sum_{i=1}^l\gamma_i\nabla G_i(x^*)-\sum_{i=1}^l\nu_i\nabla H_i(x^*)=0,$$
--   $\lambda\ge0$, $\lambda_ig_i(x^*)=0$, $\gamma_i=0$ ($i\in I_{+0}$), $\nu_i=0$ ($i\in I_{0+}$), and for every $i\in I_{00}$ either $\gamma_i>0$ and $\nu_i>0$, or $\gamma_i\nu_i=0$.
--
--   The result generalizes the convergence theorem of Kadrani et al. by replacing MPEC-LICQ with the much weaker MPEC-CPLD. It says that the relaxation method, run with parameters tending to zero, can only accumulate at M-stationary points whenever MPEC-CPLD holds there.
--
--   **Formalization Note** "Stationary point" of $R^{KDB}(t_k)$ means a feasible point with KKT multipliers (p. 5). "$\{t_k\}\downarrow 0$" is encoded as $t_k>0$, $t$ nonincreasing and $t_k\to 0$. The C¹ standing assumption of p. 1 is the hypothesis `P.IsC1`. M-stationarity (Definition 2.3(c), with the misprints of 2.3(a) corrected) requires a single multiplier tuple for both the weak-stationarity equation and the condition on $I_{00}$, and includes feasibility of $x^*$, which is not assumed. MPEC-CPLD is standard CPLD for TNLP$(x^*)$ (Definition 2.4), with linear dependence required on a whole neighbourhood of $x^*$.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 15, Theorem 3.5

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace MPECRelax.KDBConv

/-- Theorem 3.5 (p. 15): let `t_k ↓ 0` (positive, nonincreasing, tending to `0`) and let
`x^k` be a stationary (KKT) point of the relaxed program R^KDB(t_k) for every `k`. If
`x^k → xs` and MPEC-CPLD holds at `xs`, then `xs` is an M-stationary point of the
MPEC (1) (feasibility of `xs` is part of the conclusion). -/
theorem theorem_3_5 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → MPECRelax.ScholtesConv.E n) (hx : ∀ k, (P.RKDB (t k)).IsKKTPoint (x k))
    (xs : MPECRelax.ScholtesConv.E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_CPLD xs) :
    P.IsMStationary xs := by sorry

end MPECRelax.KDBConv

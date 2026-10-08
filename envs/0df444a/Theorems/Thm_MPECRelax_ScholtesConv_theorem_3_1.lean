-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_theorem_3_1
-- name    : MPECRelax.ScholtesConv.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:52:06.343162+00:00
-- url     : https://prove2.me/theorems/6623b001-9ad1-43d5-8e0f-5437ab8359c1
-- title:
--   Theorem 3.1 — limits of stationary points of Scholtes' relaxation are C-stationary under MPEC-MFCQ
-- statement:
--   Consider the MPEC (1) with continuously differentiable data $f,g_i,h_i,G_i,H_i:\mathbb R^n\to\mathbb R$. Let $\{t_k\}\downarrow0$, let $x^k$ be a stationary point of Scholtes' relaxed program
--   $$R^S(t_k):\quad\min f(x)\ \text{s.t.}\ g_i(x)\le0,\ h_j(x)=0,\ G_i(x)\ge0,\ H_i(x)\ge0,\ G_i(x)H_i(x)\le t_k,$$
--   and let $x^k\to x^*$ such that MPEC-MFCQ holds at $x^*$. Then
--
--   $$x^*\ \text{is a C-stationary point of (1)},$$
--
--   that is, $x^*$ is feasible for (1) and there are multipliers $\lambda,\mu,\gamma,\nu$ satisfying the weak-stationarity conditions of Definition 2.3(a) together with $\gamma_i\nu_i\ge0$ for all $i\in I_{00}$.
--
--   Scholtes' theorem made this conclusion under MPEC-LICQ; the paper weakens the assumption to MPEC-MFCQ, under which the KKT multipliers of the relaxed programs need not converge.
--
--   **Formalization Note** The paper states "$\{t_k\}\downarrow0$"; we state $t_k>0$, $(t_k)$ nonincreasing and $t_k\to0$. The paper states "$x^k$ is a stationary point of $R^S(t_k)$"; we state that $x^k$ is a KKT point of $R^S(t_k)$ as an NLP, feasibility included (p. 5). The standing $C^1$ assumption of p. 1 is the hypothesis `hP`. MPEC-MFCQ is Definition 2.4 (MFCQ for TNLP$(x^*)$). Feasibility of $x^*$ is not assumed; it is part of the conclusion.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 9, Theorem 3.1

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes

open Filter Topology

namespace MPECRelax.ScholtesConv

theorem theorem_3_1 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → E n) (hx : ∀ k, (P.RS (t k)).IsKKTPoint (x k))
    (xs : E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_MFCQ xs) :
    P.IsCStationary xs := by sorry

end MPECRelax.ScholtesConv

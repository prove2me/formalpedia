-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_relaxed_bound
-- name    : OfflineStochMatch.Attenuation.relaxed_bound
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-16T08:22:51.75922+00:00
-- url     : https://prove2.me/theorems/a8f2c32c-cf30-4898-9bbe-3a3449cd74ee
-- title:
--   §3.2 pp. 10–15 — $\tilde a(p_e y_e)\int_0^1$ of the product of one-sided relaxed probabilities is at least $\beta^*$
-- statement:
--   Let $G=(V,E)$ be a finite graph without parallel edges, with edge probabilities $p_f\in[0,1]$, patiences $t_r\ge 2$ ($t_r=\infty$ allowed), and $(y_f)$ feasible for LP (3). Let $\tilde a$ be $\tilde a_{\exp}(z)=e^{-z/2}$ or $\tilde a_{\mathrm{lin}}(z)=1-z/2$. For every edge $e=\{u,v\}$,
--   $$\beta^*\le \tilde a(p_e y_e)\int_0^1 \mathrm{sideProb}_u(x)\,\mathrm{sideProb}_v(x)\,dx,\qquad \beta^*=\int_0^1\big(e^{-2x}+xe^{-2x}\big)^2dx .$$
--   Here $\mathrm{sideProb}_r(x)$ is the probability, with each edge of $E(r)=\delta(r)\setminus\{e\}$ arriving before $e$ independently with probability $x$, that (1) no such early edge has $Y_f=A_f=P_f=1$, and (2) at most $t_r-1$ early edges have $Y_f=A_f=1$.
--
--   This is the analytic part of the proof of Theorem 1 (§3.2, pp. 10–15). It starts from the lower bound (8) of $\tilde a(p_ey_e)\Pr[e\text{ is safe}]$ by the integral of the product of the one-sided probabilities. It then covers the reduction of Lemma 2 ($p_e=1$, $p_f\in\{0,1\}$, saturated patience constraints), Lemma 3 (the factor $e^{-x\,y(E_1(r))}$), the Poisson and Chernoff bounds (Lemmas 4–5, Eqs. (9)–(10)), the cases $t_u\ge 3$ (Eqs. (12)–(15)) and $t_u=2$ with the exchange argument of Lemma 6 and Proposition 1, and finally Eqs. (22)–(25). **Formalization Note** The statement is about the one-sided relaxed probabilities, not about the safe event itself, and it is stated for arbitrary $p_f\in[0,1]$, that is, before the reduction of Lemma 2 to $p_f\in\{0,1\}$. The infimum $\beta^*$ is approached when $y_e\to 0$, $t_u=t_v=2$, and at each endpoint many small edges carry total $y$-mass 1 with $p=1$ and total $y$-mass 1 with $p=0$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §3.2 pp. 10–15: Lemma 2, Lemma 3, Lemmas 4–5, Eqs. (8)–(25), Lemma 6, Proposition 1

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
import Definitions.Def_OfflineStochMatch_Attenuation_SideProb

namespace OfflineStochMatch.Attenuation

theorem relaxed_bound {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, 2 ≤ t v) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) (u v : V)
    (huv : G.ends e = s(u, v)) :
    betaStar ≤ aT (p e * y e) *
      ∫ x in (0 : ℝ)..1, sideProb G p t y aT e u x * sideProb G p t y aT e v x := by sorry

end OfflineStochMatch.Attenuation

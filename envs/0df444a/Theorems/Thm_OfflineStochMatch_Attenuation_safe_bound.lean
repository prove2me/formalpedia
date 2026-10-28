-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_safe_bound
-- name    : OfflineStochMatch.Attenuation.safe_bound
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T07:28:21.28236+00:00
-- url     : https://prove2.me/theorems/2ce70691-c1e0-485f-bfd0-9cca0e05d730
-- title:
--   Theorem 1 proof, pp. 10–15 — the right-hand side of (7) is at least β*: ã(p_e y_e)·Pr[e is safe] ≥ β*
-- statement:
--   Let $G=(V,E)$ be a finite graph without parallel edges, with edge probabilities $p_f\in[0,1]$, patiences $t_v\ge 2$ for every vertex ($t_v=\infty$ allowed), and let $(y_f)_{f\in E}$ be feasible for LP (3). Let $\tilde a$ be $\tilde a_{\exp}(z)=e^{-z/2}$ or $\tilde a_{\mathrm{lin}}(z)=1-z/2$. When Algorithm 1 runs on $G$, every edge $e=\{u,v\}$ satisfies
--   $$\tilde a(p_e y_e)\cdot\Pr[e \text{ is safe}]\;\ge\;\beta^*=\int_0^1\left(e^{-2x}+xe^{-2x}\right)^2dx,$$
--   where $e$ is *safe* if, before $e$ is processed, (1) at most $t_r-1$ probes were made to edges of $\delta(r)$ for each $r\in\{u,v\}$, and (2) no edge $f\in\delta(u)\cup\delta(v)\setminus\{e\}$ processed before $e$ has $A_f=P_f=Y_f=1$.
--
--   This is the bound the paper actually establishes in the proof of Theorem 1 (pp. 10–15): after Eq. (7), $a(e)\Pr[e\text{ is free}]\ge\tilde a(p_ey_e)\Pr[e\text{ is safe}]$, the remainder of §3.2 (Lemma 2, the conditioning on $\pi(e)=x$, Lemma 3, Lemmas 4–5, the case analysis $t_u\ge3$ / $t_u=2$ with the exchange argument of Lemma 6, ending with Eq. (22)) lower bounds the right-hand side of (7) by $\beta^*$. Combined with Eq. (7) it yields Theorem 1.
--
--   **Formalization Note.** All objects (LP feasibility, `probSafe`, `expAtt`, `linAtt`, `betaStar`) are those of the shared Setting definition; the hypotheses are exactly those of Theorem 1 (`theorem_1`). Since safe implies free, this statement is stronger than Theorem 1.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §3.2 pp. 9–15: proof of Theorem 1, lower bound on the right-hand side of Eq. (7)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem safe_bound {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, 2 ≤ t v) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) :
    betaStar ≤ aT (p e * y e) * probSafe G p t y aT e := by sorry

end OfflineStochMatch.Attenuation

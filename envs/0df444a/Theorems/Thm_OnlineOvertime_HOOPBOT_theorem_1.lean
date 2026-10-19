-- Prove2me | Theorems.Thm_OnlineOvertime_HOOPBOT_theorem_1
-- name    : OnlineOvertime.HOOPBOT.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:53.75714+00:00
-- url     : https://prove2.me/theorems/2a6684e6-1c47-4edc-b297-a797e9a112a6
-- title:
--   Theorem 1, p. 14 — HOOP-BOT with θ1 = θ2 = θ∗ is (1 − 2γmaxRmax)/(1 + θ∗)-competitive
-- statement:
--   Let an instance of online scheduling with budgeted overtime satisfy the standing assumptions, and run Algorithm 1 (HOOP-BOT) with $\theta_1=\theta_2=\theta^*$ and any tie-break for the argmax of Step 3; let $(y,v)$ be the assignment and the overtime it produces. Let
--   $$r=\frac{1-2\gamma_{\max}R_{\max}}{1+\theta^*},$$
--   with $\gamma_{\max}$, $R_{\max}$, $\alpha$ as in (1), $\lambda$, $\zeta$ as in Theorem 1 and $\theta^*$ as in (11). Then there is a solution $(\tilde y,\tilde v)$ obtained by converting $(y,v)$, namely
--
--   1. $(\tilde y,\tilde v)$ is feasible for the offline problem (P);
--   2. $\tilde y\le y$ and $\tilde v\le v$ entrywise;
--   3. for each server-date $(i,t)$, $\tilde y_{i,j,t}$ differs from $y_{i,j,t}$ for at most two customers $j$;
--
--   such that, with $f^*$ the optimal value of (P) (the greatest objective value $\sum_{t,i,j}c_{i,j}y'_{i,j,t}-\sum_{t,i}d_iv'_{i,t}$ of a feasible solution $(y',v')$),
--   $$\tilde f_P=\sum_{t,i,j}c_{i,j}\tilde y_{i,j,t}-\sum_{t,i}d_i\tilde v_{i,t}\ \ge\ r\,f^*.$$
--   In the paper's words, HOOP-BOT admits the competitive ratio $r$.
--
--   This is the main result of the paper: a worst-case guarantee, against an adversarial arrival sequence, for scheduling with overtime by an online primal-dual method.
--
--   **Formalization Note** "Admits the competitive ratio $r$" is Definition 1 with $Z_{ALG}=\tilde f_P$, the value of "the feasible solution obtained by converting the almost feasible solution" (Proposition 4); that solution is described only in the proof of Proposition 4 (p. 25: $\tilde y\le y$, $\tilde v\le v$, only $y$ at the iterations $K_1$, $K_2$ and $v$ changed), which the three clauses above pin. $f^*$ enters as any greatest element of the set of feasible objective values (the maximum exists: $y$ is binary and the zero solution is feasible), so no supremum junk value is used. The coefficients are $\theta_1=\theta_2=\theta^*$ as stated in Lemma 2. $\theta^*$ depends on the whole instance, as in the paper. The statement is posed exactly as printed, including $u_{i,t}=1$ initially; the proposers record a counterexample to it.
-- source:
--   Keyvanshokooh, Shi, Van Oyen, Online Advance Scheduling with Overtime: A Primal-Dual Approach, accepted manuscript (MSOM, accepted May 2019; SSRN 3352166), p. 14, Theorem 1 (with Definition 1, p. 13, and Proposition 4, (23), p. 24)

import Mathlib
import Definitions.Def_OnlineOvertime_HOOPBOT_Model

namespace OnlineOvertime.HOOPBOT

/-- Theorem 1 (Competitive Ratio Analysis of the HOOP-BOT), p. 14, read through Proposition 4,
(23), p. 24, and Definition 1, p. 13. Run Algorithm 1 with `θ1 = θ2 = θ∗` of (11) and any argmax
tie-break. The almost-feasible output `(y, v)` can be converted into a feasible solution
`(ỹ, ṽ)` of (P) with `ỹ ≤ y`, `ṽ ≤ v`, changing at most two customers per server-date, whose
objective is at least `r = (1 − 2γmax Rmax)/(1 + θ∗)` times the optimal value `f∗` of (P)
(the greatest objective value of a feasible solution). -/
theorem theorem_1 {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) (hsel : IsArgmaxSelector sel) :
    let s := run I (thetaStar I) (thetaStar I) sel
    ∃ (yt : Fin m → Fin n → Fin T → ℝ) (vt : Fin n → Fin T → ℝ),
      Feasible I yt vt ∧ (∀ j i t, yt j i t ≤ s.y j i t) ∧ (∀ i t, vt i t ≤ s.v i t) ∧
      (∀ i t, (Finset.univ.filter (fun j => yt j i t ≠ s.y j i t)).card ≤ 2) ∧
      ∀ fstar : ℝ,
        IsGreatest {f : ℝ | ∃ (y : Fin m → Fin n → Fin T → ℝ) (v : Fin n → Fin T → ℝ),
          Feasible I y v ∧ obj I y v = f} fstar →
        ratio I * fstar ≤ obj I yt vt := by sorry

end OnlineOvertime.HOOPBOT

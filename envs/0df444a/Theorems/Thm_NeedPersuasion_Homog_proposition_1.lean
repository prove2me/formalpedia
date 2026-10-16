-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_proposition_1
-- name    : NeedPersuasion.Homog.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:53.669021+00:00
-- url     : https://prove2.me/theorems/11aa622a-acc2-49f1-a02c-0043bf48f314
-- title:
--   Proposition 1, p. 16 — with λ_H = 0, W_L(fi) ≥ β_fi · W_L(sm), β_fi ≥ 1 − 1/(m_fi+1), with equality iff W_L(m_fi) ≥ W_L(m_fi − 1)
-- statement:
--   Consider the congested-service model under its standing assumptions in the homogeneous setting $\lambda_H = 0$: only low-need users arrive, at rate $\lambda_L \in (0,1]$. Let $m_{fi}$ be the full-information threshold (the least $k$ with $u_L(k) < 0$), $\mathrm{fi}$ the full-information mechanism, $W_L(x)$ the L-welfare of the threshold policy with threshold $x$, and
--   $$\beta_{fi} = \frac{\sum_{n=0}^{m_{fi}-1}\lambda_L^n}{\sum_{n=0}^{m_{fi}}\lambda_L^n}.$$
--   Then:
--
--   1. every signaling mechanism $\pi \in \Pi_{SM}$ satisfies
--   $$W_L(\mathrm{fi}) \ge \beta_{fi}\, W_L(\pi);$$
--   2. $\beta_{fi} \ge 1 - \dfrac{1}{m_{fi}+1}$;
--   3. full information is optimal, i.e. $W_L(\pi) \le W_L(\mathrm{fi})$ for all $\pi \in \Pi_{SM}$, if and only if $W_L(m_{fi}) \ge W_L(m_{fi}-1)$.
--
--   The paper states this as $W_L(\mathrm{fi}) \ge \beta_{fi}\, W_L(\mathrm{sm})$ for the optimal signaling mechanism $\mathrm{sm}$, with equality $W_L(\mathrm{fi}) = W_L(\mathrm{sm})$ if and only if $W_L(m_{fi}) \ge W_L(m_{fi}-1)$. With a single type of user, information design can therefore improve on full information by a factor of at most $1/\beta_{fi} \le 1 + 1/m_{fi}$.
--
--   **Formalization Note** The optimal mechanism $\mathrm{sm}$ is not introduced as an object: part 1 is asserted for every $\pi \in \Pi_{SM}$, which implies the paper's inequality for any maximizer, and "$W_L(\mathrm{fi}) = W_L(\mathrm{sm})$" is read as "$\mathrm{fi}$ attains the maximum of $W_L$ over $\Pi_{SM}$" (note $\mathrm{fi} \in \Pi_{SM}$). Both readings coincide with the paper's whenever a maximizer exists, and need no existence result. $W_L(m_{fi}-1)$ uses the real number $m_{fi}-1 \ge 0$, since $m_{fi} \ge 1$.
-- source:
--   arXiv:2005.07253v3, Proposition 1, p. 16; proof App. C, p. 40

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model
import Definitions.Def_NeedPersuasion_Homog_BetaFi

namespace NeedPersuasion.Homog

theorem proposition_1 (M : Model) (hM : M.Standing) (hH : M.lamH = 0) :
    (∀ π ∈ PiSM M, betaFi M * WL M π ≤ WL M (fi M)) ∧
      1 - 1 / ((mfi M : ℝ) + 1) ≤ betaFi M ∧
      ((∀ π ∈ PiSM M, WL M π ≤ WL M (fi M)) ↔
        WLx M ((mfi M : ℝ) - 1) ≤ WLx M (mfi M)) := by sorry

end NeedPersuasion.Homog

-- Prove2me | Theorems.Thm_LeveragedPayouts_ShockSize_proposition_12
-- name    : LeveragedPayouts.ShockSize.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:04.73702+00:00
-- url     : https://prove2.me/theorems/8e1a2ecc-c89e-4322-95ae-7b6eae5852ab
-- title:
--   Proposition 12, p. 32 — there is $\bar\rho\in[0,1)$: for $\rho\ge\bar\rho$ the optimal date-0 rate is $R$, for $\rho<\bar\rho$ it is cut below $R$
-- statement:
--   Fix an economy (with $f,g,\pi,R$ and hence $l^*,w^*$ held fixed while the shock $\rho$ varies). There exists $\bar\rho$ with $0\le\bar\rho<1$ such that:
--
--   1. **Small shocks.** For every $\rho\in(0,1)$ with $\rho\ge\bar\rho$, it is optimal to leave the date-0 rate at its steady-state value: $r_u=R$ with labour $l_u=l^*$ is an optimal rate. If moreover $\rho>\bar\rho$, it is the only optimum: every optimal $(r_u,l_u)$ equals $(R,l^*)$. Productive efficiency is at the first-best, $e(R)=\pi$, while investment is strictly below the first-best: $l^*<l_\rho$ for every first-best labour $l_\rho$ at $\rho$.
--
--   2. **Large shocks.** For every $\rho\in(0,\bar\rho)$ (an empty range when $\bar\rho=0$), an optimal rate exists, and every optimal rate $r_u$ with labour $l_u$ is accommodative and leaves both efficiency and investment below the first-best:
--   $$r_u<R,\qquad e(r_u)<\pi,\qquad l^*<l_u<l_\rho$$
--   for every first-best labour $l_\rho$ at $\rho$.
--
--   The proposition describes how the optimal response of monetary policy to a productivity shock $1-\rho$ trades off productive efficiency against scale: small shocks are met by "leaning against the wind", large shocks possibly by a rate cut.
--
--   **Formalization Note** The printed proposition says "$l_u<l^*$" in both bullets. This cannot be meant: in the first bullet $r_u=R$ gives $l_u=l^*$, and in the second the paper's proof states $l_u>l^*$ when $r_u<R$ (p. 58). The prose "investment is strictly below the first-best level" fixes the reading $l_u<l_\rho$, which is what is formalized, together with $l^*<l_u$ in the second bullet. The paper's $e^*$ is the effort $e(r_u)$ at the optimal rate. Uniqueness of the optimum at $\rho=\bar\rho$ itself is not claimed, since an interior optimum and $R$ may tie there. The comparison "$R>r_\rho$" with the regulated rate of Proposition 10 is not formalized (it needs the regulated economy). The planner may choose any rate $r>0$; rates above $R$ enter through $\bar r(r)=\min\{r,R\}$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 32, Proposition 12; proof in Appendix B, pp. 57–58

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.ShockSize

theorem proposition_12 (E : LeveragedPayouts.Unregulated.Economy) :
    ∃ ρbar : ℝ, 0 ≤ ρbar ∧ ρbar < 1 ∧
      (∀ ρ, 0 < ρ → ρbar ≤ ρ → ρ < 1 →
        LeveragedPayouts.Unregulated.IsOptimalRate E ρ E.R E.lstar ∧
          (ρbar < ρ → ∀ ru lu, LeveragedPayouts.Unregulated.IsOptimalRate E ρ ru lu → ru = E.R ∧ lu = E.lstar) ∧
          LeveragedPayouts.Unregulated.effort E E.R = E.π ∧
          ∀ lρ, LeveragedPayouts.Unregulated.IsFirstBestLabor E ρ lρ → E.lstar < lρ) ∧
      (∀ ρ, 0 < ρ → ρ < ρbar →
        (∃ ru lu, LeveragedPayouts.Unregulated.IsOptimalRate E ρ ru lu) ∧
          ∀ ru lu, LeveragedPayouts.Unregulated.IsOptimalRate E ρ ru lu →
            ru < E.R ∧ LeveragedPayouts.Unregulated.effort E ru < E.π ∧ E.lstar < lu ∧
              ∀ lρ, LeveragedPayouts.Unregulated.IsFirstBestLabor E ρ lρ → lu < lρ) := by sorry

end LeveragedPayouts.ShockSize

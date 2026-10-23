-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_proposition_11
-- name    : LeveragedPayouts.Unregulated.proposition_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:27.387008+00:00
-- url     : https://prove2.me/theorems/53bf5bb1-24f8-4bbc-bfb8-09e46fdfe3fd
-- title:
--   Proposition 11 (points 1–2), p. 31 — with unregulated leverage an optimal date-0 rate exists, is at most R, and leaves date-0 labour and surplus strictly below the first-best
-- statement:
--   Consider the economy of the mission: discount rate $R>1$, effort parameter $\pi\in(0,1)$, technologies $f$ and $g$ satisfying the Inada conditions, and the steady state $(l^*,w^*)$ of (20). The date-0 cohort of workers is hit by a productivity shock $\rho\in(0,1)$, the wage cannot fall below $w^*$ at date 0, and leverage is not regulated. Let $l_\rho$ be the first-best date-0 labour, $\pi f'(l_\rho)/(2R)=\rho g'(1-l_\rho)$.
--
--   The planner chooses the date-0 rate $r>0$; entrepreneurs respond with effort $e(r)=\pi R/(2R-\min\{r;R\})$ and labour demand $l(r)$, and the date-0 surplus is
--   $$\Sigma_\rho=\Big(e-\frac{e^2}{2\pi}\Big)\frac{f(l)}{R}+\rho\,g(1-l).$$
--   Then an optimal date-0 rate exists, and every optimal rate $r_u$ with labour $l_u$ satisfies
--   1. $r_u\le R$;
--   2. $l_u<l_\rho$: entrepreneurs hire strictly less labour than at the first-best;
--   3. the date-0 surplus is strictly below its first-best value:
--   $$\Big(e(r_u)-\frac{e(r_u)^2}{2\pi}\Big)\frac{f(l_u)}{R}+\rho\,g(1-l_u)<\frac{\pi f(l_\rho)}{2R}+\rho\,g(1-l_\rho).$$
--
--   This is the date-0 content of points 1 and 2 of Proposition 11: monetary easing cannot restore the first-best when leverage is unregulated, because cutting the rate to raise investment also triggers leveraged payouts that degrade effort.
--
--   **Formalization Note** The planner may choose any $r>0$; for $r>R$ the firm's response is Proposition 2 with $\bar r(r)=R$. The paper's proof restricts to "$r\le 1$" (a misprint for $r\le R$); allowing $r>R$ makes $r_u\le R$ a conclusion. Proposition 11's comparison "than when [leverage] is [regulated]" is stated against the first-best date-0 surplus, which regulated leverage attains (Proposition 10); other dates are not modelled. Point 1's "$r^*=R$ at all dates other than 0" and point 3 are not part of this statement.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 31, Proposition 11 (points 1–2); proof p. 56, (59)–(60)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.Unregulated
theorem proposition_11 (E : Economy) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (lρ : ℝ)
    (hlρ : IsFirstBestLabor E ρ lρ) :
    (∃ ru lu, IsOptimalRate E ρ ru lu) ∧
    ∀ ru lu, IsOptimalRate E ρ ru lu →
      ru ≤ E.R ∧ lu < lρ ∧ surplus E ρ (effort E ru) lu < surplus E ρ E.π lρ := by sorry
end LeveragedPayouts.Unregulated

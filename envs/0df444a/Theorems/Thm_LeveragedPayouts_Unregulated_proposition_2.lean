-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_proposition_2
-- name    : LeveragedPayouts.Unregulated.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:09.68996+00:00
-- url     : https://prove2.me/theorems/26c420dc-7a20-4c65-a640-72f1c477001d
-- title:
--   Proposition 2, pp. 15–16 — the firm's skin in the game, effort and investment (8) with r̄(r) = min{r; R}
-- statement:
--   Let $R>1$, $\pi\in(0,1)$, $W\in\mathbb R$, let $f$ satisfy the Inada conditions and let the market rate be $r>0$. Write $\bar r(r)=\min\{r;R\}$.
--
--   1. If $r\ge R$, program (3) has a solution, and every solution $(e,I)$ satisfies
--   $$e=\pi\cdot\frac{R}{2R-\bar r(r)}\;(=\pi),\qquad \frac{\pi R f'(I)}{2(2R-\bar r(r))}=r .$$
--   2. If $r<R$, program (5)–(6) has a solution, and every solution $(e,I,x)$ satisfies
--   $$x=\frac{R}{2R-\bar r(r)},\qquad e=\pi x,\qquad \frac{\pi R f'(I)}{2(2R-\bar r(r))}=r .$$
--
--   Together these are the conditions (8) of Proposition 2: for $r\ge R$ the firm keeps its whole output ($x=1$) and exerts the first-best effort $\pi$; for $r<R$ it sells a fraction $1-x$ of its output (a leveraged payout) and its effort falls below $\pi$.
--
--   **Formalization Note** The comparative-statics bullets of Proposition 2 are not part of this statement. The hypothesis "W sufficiently large" only guarantees that the debt is risk-free; $W$ is an arbitrary real here, as it does not affect the maximizers. In case 1 the paper's program (3) has no stake variable; its $x=R/(2R-\bar r)=1$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), pp. 15–16, Proposition 2, (8); programs (3), (5), (6), pp. 13–14

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Firm

namespace LeveragedPayouts.Unregulated
theorem proposition_2 (π R W r : ℝ) (hR : 1 < R) (hπ0 : 0 < π) (hπ1 : π < 1) (f : ℝ → ℝ)
    (hf : IsInada f) (hr : 0 < r) :
    (R ≤ r →
      (∃ e I, IsMax3 π R W r f e I) ∧
      ∀ e I, IsMax3 π R W r f e I →
        e = π * (R / (2 * R - min r R)) ∧
        π * R * deriv f I / (2 * (2 * R - min r R)) = r) ∧
    (r < R →
      (∃ e I x, IsMax5 π R W r f e I x) ∧
      ∀ e I x, IsMax5 π R W r f e I x →
        x = R / (2 * R - min r R) ∧ e = π * x ∧
        π * R * deriv f I / (2 * (2 * R - min r R)) = r) := by sorry
end LeveragedPayouts.Unregulated

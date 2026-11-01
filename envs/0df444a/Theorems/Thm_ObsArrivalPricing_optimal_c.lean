-- Prove2me | Theorems.Thm_ObsArrivalPricing_optimal_c
-- name    : ObsArrivalPricing.optimal_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:42:59.576784+00:00
-- url     : https://prove2.me/theorems/003b6750-409c-4737-ab19-cd57caaccab3
-- title:
--   Proof of Theorem 1, p.23 — the optimal $c$ and the constant $4.911$
-- statement:
--   Let $w^\star=W_{-1}(-1/(2\sqrt e))$, with $W_{-1}$ the negative branch of the Lambert function, $c^\star=e^{w^\star+1/2}$, and
--   $$g(c)=\frac{2\ln(1/c)}{(1-c)^2},\qquad C=-\frac{2w^\star+1}{\big(e^{w^\star+1/2}-1\big)^2}.$$
--   Then
--
--   1. $c^\star\in(0,1)$;
--   2. $c^\star$ minimizes $g$ over $(0,1)$;
--   3. $g(c^\star)=C$;
--   4. $0.284<c^\star<0.285$;
--   5. $4.91<C<4.911$.
--
--   Together with Lemma 3 (the ratio $R_\tau/R^{uo}_\tau$ is at most $g(c)$ for every $c\in(0,1)$), this gives the constant of Theorem 1.
--
--   Differences from the source:
--   - encoding: "$c\approx0.284$", "roughly 4.911" → $0.284<c^\star<0.285$ and $4.91<C<4.911$; reason: $c^\star=0.28467\ldots$ and $C=4.91081\ldots$; the two-sided bounds are the exact content of the approximations
--   - encoding: $W_{-1}$, "the branch satisfying $W(x)\le-1$" (endnote 6) → `ValuePersPricing.Deviation.lambertWm1`, the unique $w\le-1$ with $we^w=x$ when it exists; reason: $-1/(2\sqrt e)\in(-1/e,0)$, where the two agree
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), proof of Theorem 1, p.23; endnote 6, p.25

import Mathlib
import Definitions.Def_ObsArrivalPricing_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- The optimal constant in the proof of Theorem 1 (SSRN 3541494, p.23: "This bound ratio holds for
any constant c ∈ (0,1), and it is minimized at c = e^{W₋₁(−1/(2√e))+1/2} ≈ 0.284, giving a minimum of
−(2W₋₁(−1/(2√e))+1)/(e^{W₋₁(−1/(2√e))+1/2}−1)², which is roughly 4.911"). The point
`c⋆ = e^{W₋₁(−1/(2√e))+1/2}` lies in `(0,1)`, minimizes `2 ln(1/c)/(1 − c)²` over `(0,1)` with minimum
value the bound of Theorem 1, and `0.284 < c⋆ < 0.285`, `4.91 < C < 4.911`. -/
theorem optimal_c :
    cStar ∈ Ioo (0 : ℝ) 1 ∧ IsMinOn ratioBound (Ioo (0 : ℝ) 1) cStar ∧
      ratioBound cStar = voBound ∧ (0.284 : ℝ) < cStar ∧ cStar < 0.285 ∧
      (4.91 : ℝ) < voBound ∧ voBound < 4.911 := by sorry

end ObsArrivalPricing

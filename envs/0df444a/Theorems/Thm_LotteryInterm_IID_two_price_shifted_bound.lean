-- Prove2me | Theorems.Thm_LotteryInterm_IID_two_price_shifted_bound
-- name    : LotteryInterm.IID.two_price_shifted_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:49.472126+00:00
-- url     : https://prove2.me/theorems/587b3334-9b59-4abe-a486-9f65111c80c6
-- title:
--   §6.2.1 — two prices approximate shifted optimal revenue
-- statement:
--   Let $n\ge1$ bidders be independent with the same regular value law $F$, satisfying the vanishing-tail condition and $\operatorname{OPT}>0$. Set $\tau=2\operatorname{OPT}$. For every $\delta>0$ there exists a finite $T\ge\tau$ such that the seller's menu choosing prices $\tau$ and $T$ with probability $1/2$ each has a best response and satisfies
--   $$\operatorname{RandMI}(M(\tau,T,1/2))\ge(1/8-\delta)\operatorname{OPT}_{\tau}.$$
--   The guarantee ranges over every intermediary best response. Finiteness of $\operatorname{OPT}$ is concluded.
--
--   This is the quantitative two-price conclusion inside the proof of Theorem 6.3; the existential menu avoids assuming that the strict-tail price set has a maximum.
--
--   Differences from the source:
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary; reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee, including when a coefficient is nonpositive
--   - encoding: finite positive optimal revenue in the numerical cutoff formulas → finiteness is a conclusion and the real cutoff uses EReal.toReal; reason: regularity and the vanishing-tail assumption imply finiteness; finiteness is never assumed as a replacement for those facts
--   - reading: taking epsilon to zero gives the coefficient 1/8 → every positive delta has a finite menu with coefficient 1/8 minus delta; reason: the paper uses a family of discounted menus and does not establish a limiting menu; this retains every finite-discount guarantee without assuming attainment
--   - encoding: regular distribution with a PDF on its support [a, b]: phi(y) - phi(x) >= 0 for all a <= x <= y <= b (Definition A.2) → ValueDist with density positive on (a, b) and an optional terminal atom; Regular asks phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law, and with f(a) = 0 the source formula gives phi(a) = -infinity, which meets the monotonicity at a; a zero density inside (a, b) would make phi = -infinity at an interior point, which regularity excludes; the two classes of laws coincide
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §6.2.1, proof of Theorem 6.3, p.21 (PDF p.22); menu on p.19 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

/-- The p.21 conclusion with an arbitrarily small loss, rather than an
unjustified limiting menu or a maximum of a discontinuous strict-tail curve. -/
theorem two_price_shifted_bound {n : ℕ} (hn : 0 < n) (F : ValueDist)
    (hreg : Regular F) (htail : VanishingTail F)
    (hopt : 0 < OPT (fun _ : Fin n => F)) (δ : ℝ) (hδ : 0 < δ) :
    OPT (fun _ : Fin n => F) < ⊤ ∧
    ∃ (T : ℝ) (hτ : 0 ≤ 2 * (OPT (fun _ : Fin n => F)).toReal)
      (hT : 2 * (OPT (fun _ : Fin n => F)).toReal ≤ T),
      let M := twoPrice (2 * (OPT (fun _ : Fin n => F)).toReal) T (1 / 2) hτ hT
        (by constructor <;> norm_num)
      (∃ I, BestResponse (fun _ : Fin n => F) M I) ∧
      (((1 / 8 - δ : ℝ) : EReal) *
        shiftedOPT (fun _ : Fin n => F) (2 * (OPT (fun _ : Fin n => F)).toReal)) ≤
        RandMI (fun _ : Fin n => F) M := by sorry

end LotteryInterm.IID

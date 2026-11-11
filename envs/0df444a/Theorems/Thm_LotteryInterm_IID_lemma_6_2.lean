-- Prove2me | Theorems.Thm_LotteryInterm_IID_lemma_6_2
-- name    : LotteryInterm.IID.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:10.055412+00:00
-- url     : https://prove2.me/theorems/1d5d1b86-f420-46ae-88b1-eab71cc4815b
-- title:
--   Lemma 6.2 — deterministic and shifted-revenue decomposition
-- statement:
--   Let $n\ge1$ independent regular bidders satisfy the vanishing-tail condition and $\operatorname{OPT}>0$. For any $H>\operatorname{OPT}/2$,
--   $$\operatorname{DET}\log(2H/\operatorname{OPT})+\operatorname{OPT}_H\ge\operatorname{OPT}/2.$$
--   The logarithm is natural and its argument exceeds one. Moreover, if a two-price menu $M$ earns at least $c\operatorname{OPT}_H$, then there exists a menu $M'$ equal either to $M$ or to a deterministic posted price such that
--   $$\operatorname{RandMI}(M')\ge\min\!\left\{\frac1{4\log(2H/\operatorname{OPT})},\frac c4\right\}\operatorname{OPT}.$$
--   A best response to $M'$ exists. No attainment of the supremum defining $\operatorname{DET}$ is assumed. The first conclusion includes finiteness of $\operatorname{OPT}$.
--
--   Both clauses of the source decomposition are stated in one item.
--
--   Differences from the source:
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary; reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee, including when a coefficient is nonpositive
--   - encoding: finite positive optimal revenue in the numerical cutoff formulas → finiteness is a conclusion and the real cutoff uses EReal.toReal; reason: regularity and the vanishing-tail assumption imply finiteness; finiteness is never assumed as a replacement for those facts
--   - reading: the second sentence writes OPT_T although only H is fixed → OPT_H is used in the second sentence; reason: the lemma has no T and its application on p.23 sets H equal to T
--   - reading: two-price menu → the lottery menu includes equal prices and zero weights; reason: the lemma expressly allows its output to be deterministic
--   - generalization: a positive approximation factor c is implicit → c ranges over all real numbers; reason: the nonpositive case is immediate from nonnegative seller revenue
--   - encoding: regular distribution with a PDF on its support [a, b]: phi(y) - phi(x) >= 0 for all a <= x <= y <= b (Definition A.2) → ValueDist with density positive on (a, b) and an optional terminal atom; Regular asks phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law, and with f(a) = 0 the source formula gives phi(a) = -infinity, which meets the monotonicity at a; a zero density inside (a, b) would make phi = -infinity at an interior point, which regularity excludes; the two classes of laws coincide
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Lemma 6.2, pp.17–18 (PDF pp.18–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

/-- OPT_T in the lemma's second sentence is read as OPT_H, its only cutoff.
Finiteness is concluded, so toReal is not a finiteness hypothesis. -/
theorem lemma_6_2 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist)
    (hreg : ∀ i, Regular (D i)) (htail : ∀ i, VanishingTail (D i))
    (hopt : 0 < OPT D) (H : ℝ) (hH : (OPT D).toReal / 2 < H) :
    OPT D < ⊤ ∧
    OPT D / 2 ≤ DET D * ((Real.log (2 * H / (OPT D).toReal) : ℝ) : EReal) +
      shiftedOPT D H ∧
    (∀ (a b weight c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
      (hw : weight ∈ Set.Icc 0 1),
      (c : EReal) * shiftedOPT D H ≤ RandMI D (twoPrice a b weight ha hab hw) →
      ∃ M' : Menu,
        (M' = twoPrice a b weight ha hab hw ∨ ∃ (p : ℝ) (hp : 0 ≤ p), M' = postedPrice p hp) ∧
        (∃ I, BestResponse D M' I) ∧
        ((min (1 / (4 * Real.log (2 * H / (OPT D).toReal))) (c / 4) : ℝ) : EReal) *
          OPT D ≤ RandMI D M') := by sorry

end LotteryInterm.IID

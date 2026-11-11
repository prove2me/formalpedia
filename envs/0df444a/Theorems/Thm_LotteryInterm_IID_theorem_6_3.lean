-- Prove2me | Theorems.Thm_LotteryInterm_IID_theorem_6_3
-- name    : LotteryInterm.IID.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:14.906536+00:00
-- url     : https://prove2.me/theorems/c142c771-7a39-49b5-bf6a-edc865d49c8b
-- title:
--   Theorem 6.3 — a two-price lottery guarantees constant seller revenue
-- statement:
--   Let $n\ge1$ bidders have independent identically distributed nonnegative values from a regular law $F$, with density on its possibly unbounded interval support and an optional finite terminal atom. Suppose $v\Pr[V>v]\to0$ and the optimal direct Myerson revenue $\operatorname{OPT}$ is positive. For every $\delta>0$ there are $0\le a\le b$ and $\lambda\in[0,1]$ such that the two-price seller menu $M=M(a,b,\lambda)$ has an intermediary best response and
--   $$\operatorname{RandMI}(M)\ge(1/32-\delta)\operatorname{OPT}.$$
--   The infimum defining $\operatorname{RandMI}$ ranges over every revenue-maximizing intermediary. The optimum is finite. Prices and lottery weights are chosen before bidder values are realized; $1/32$ is absolute, independent of $n,F$, and the menu.
--
--   The paper writes Ω(1); the proof yields 1/32 − δ for every δ > 0. This is the full iid intermediated-seller result, including $n=1$, unbounded supports, and terminal atoms.
--
--   Differences from the source:
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary; reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee, including when a coefficient is nonpositive
--   - encoding: finite positive optimal revenue in the numerical cutoff formulas → finiteness is a conclusion and the real cutoff uses EReal.toReal; reason: regularity and the vanishing-tail assumption imply finiteness; finiteness is never assumed as a replacement for those facts
--   - generalization: the guarantee is written Omega of one times OPT → the explicit coefficient is 1/32 minus delta for every positive delta; reason: Lemma 6.2 with H equal to twice OPT and the p.21 bound give this absolute coefficient; delta equal to 1/64 gives a universal positive factor
--   - reading: two-price randomized mechanism → at most two support prices including equal prices and endpoint weights; reason: Lemma 6.2 allows a deterministic posted price and p.23 explicitly says at most two prices
--   - encoding: regular distribution with a PDF on its support [a, b]: phi(y) - phi(x) >= 0 for all a <= x <= y <= b (Definition A.2) → ValueDist with density positive on (a, b) and an optional terminal atom; Regular asks phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law, and with f(a) = 0 the source formula gives phi(a) = -infinity, which meets the monotonicity at a; a zero density inside (a, b) would make phi = -infinity at an interior point, which regularity excludes; the two classes of laws coincide
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 6.3, p.19 (PDF p.20), proof pp.19–21 (PDF pp.20–22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

/-- The full i.i.d. theorem: the absolute constant is the proof's 1/32, with
arbitrarily small loss. Existence and a guarantee for every best response are
explicit, even when δ ≥ 1/32. The menu is chosen before any realized profile. -/
theorem theorem_6_3 {n : ℕ} (hn : 0 < n) (F : ValueDist)
    (hreg : Regular F) (htail : VanishingTail F)
    (hopt : 0 < OPT (fun _ : Fin n => F)) (δ : ℝ) (hδ : 0 < δ) :
    OPT (fun _ : Fin n => F) < ⊤ ∧
    ∃ (a b weight : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hw : weight ∈ Set.Icc 0 1),
      let M := twoPrice a b weight ha hab hw
      (∃ I, BestResponse (fun _ : Fin n => F) M I) ∧
      (((1 / 32 - δ : ℝ) : EReal) * OPT (fun _ : Fin n => F)) ≤
        RandMI (fun _ : Fin n => F) M := by sorry

end LotteryInterm.IID

-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_6_1
-- name    : LotteryInterm.IID.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:11:38.299231+00:00
-- url     : https://prove2.me/theorems/02bdceae-b363-4812-9e42-226a009a2c45
-- title:
--   Theorem 6.1 — one bidder: a two-price lottery guarantees $\mathrm{OPT}/4$
-- statement:
--   Let a single bidder have a regular value law $F$, with density on a possibly unbounded interval and an optional finite terminal atom, satisfying $v\Pr[V>v]\to0$, with optimal revenue $\mathrm{OPT}>0$. Then there are prices $0\le a\le b$ and a weight $\lambda\in[0,1]$ such that the seller menu $M(a,b,\lambda)$ — price $a$ with probability $\lambda$, else $b$ — has an intermediary best response and
--   $$\mathrm{RandMI}(M)\ \ge\ \frac{\mathrm{OPT}}{4}$$
--   against every revenue-maximizing intermediary. The optimum is finite.
--
--   The constant is the printed $1/4$, attained by one menu (the paper's proof exhibits menus earning $(1-\varepsilon)\mathrm{OPT}/4$ and lets $\varepsilon\to0$). This is the single-bidder base case of the randomized guarantees of §6.
--
--   Differences from the source:
--   - reading: two-price seller menu → at most two support prices, equal prices and endpoint weights allowed; reason: the published twoPrice menu; the proof's menu uses prices 0 and (1 - eps) p with probability 1/2 each
--   - encoding: finite positive OPT → finiteness is a conclusion; reason: it follows from the hypotheses
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary (RandMI is the infimum over all best responses); reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent, and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: regular distribution with a PDF on its support [a, b] (Definition A.2 with alpha = 0) → the published ValueDist (density positive on (a, b), optional terminal atom, phi(b) = b) with Regular asking phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law; the two classes of laws coincide (same encoding as the published mission)
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 6.1, p.16 (PDF p.17); proof pp.16–17 (PDF pp.17–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Intermediary

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 6.1: one bidder; a menu with at most two prices has an intermediary best
response and guarantees `OPT / 4` against every best response. -/
theorem theorem_6_1 (F : ValueDist) (hreg : Regular F) (htail : VanishingTail F)
    (hopt : 0 < OPT (fun _ : Fin 1 => F)) :
    OPT (fun _ : Fin 1 => F) < ⊤ ∧
    ∃ (a b weight : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hw : weight ∈ Set.Icc 0 1),
      let M := twoPrice a b weight ha hab hw
      (∃ I, BestResponse (fun _ : Fin 1 => F) M I) ∧
      (((1 / 4 : ℝ) : EReal) * OPT (fun _ : Fin 1 => F)) ≤
        RandMI (fun _ : Fin 1 => F) M := by sorry

end LotteryInterm.IID.Supplement

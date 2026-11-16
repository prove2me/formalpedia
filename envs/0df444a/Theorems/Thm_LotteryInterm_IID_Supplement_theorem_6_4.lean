-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_6_4
-- name    : LotteryInterm.IID.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:01.203205+00:00
-- url     : https://prove2.me/theorems/c1a371d4-7e6b-4a6a-8b15-77c98ec837a2
-- title:
--   Theorem 6.4 — non-identical bidders: a two-price lottery guarantees $(1/(32n)-\delta)\,\mathrm{OPT}$
-- statement:
--   Let $n\ge1$ bidders have independent, possibly non-identical regular value laws $D_1,\dots,D_n$ (densities on possibly unbounded intervals, optional finite terminal atoms), each with $v\Pr[V_i>v]\to0$, and $\mathrm{OPT}>0$. For every $\delta>0$ there are $0\le a\le b$ and $\lambda\in[0,1]$ such that the two-price menu $M=M(a,b,\lambda)$ has an intermediary best response and
--   $$\mathrm{RandMI}(M)\ \ge\ \Big(\frac1{32n}-\delta\Big)\mathrm{OPT}$$
--   against every revenue-maximizing intermediary; $\mathrm{OPT}$ is finite.
--
--   The paper writes $\Omega(1/n)\,\mathrm{OPT}$; the proof yields $1/(32n)-\delta$ for every $\delta>0$ (Lemma 6.2 with $H=\tau=2\mathrm{OPT}$, natural logarithm, and the menu bound $\mathrm{OPT}_\tau/(8n)$ after $\varepsilon\to0$). This extends the i.i.d. goal Theorem 6.3 to non-identical bidders at the cost of a factor $n$.
--
--   Differences from the source:
--   - generalization: RandMI(MS) = Omega(1/n) OPT → the explicit coefficient 1/(32 n) - delta for every delta > 0; reason: Lemma 6.2 with H = tau = 2 OPT gives DET log 4 + OPT_tau >= OPT/2, and the p.23 menu gives OPT_tau/(8n) - eps terms, so min{1/(4 log 4), (1/(8n))/4} = 1/(32n) up to delta; delta = 1/(64 n) gives the source's Omega(1/n) with an absolute constant
--   - reading: two-price randomized mechanism → at most two support prices, equal prices and endpoint weights allowed; reason: Lemma 6.2 allows a posted price; same reading as the published goal
--   - encoding: finite positive OPT → finiteness is a conclusion; reason: it follows from the hypotheses
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary (RandMI is the infimum over all best responses); reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent, and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: regular distribution with a PDF on its support [a, b] (Definition A.2 with alpha = 0) → the published ValueDist (density positive on (a, b), optional terminal atom, phi(b) = b) with Regular asking phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law; the two classes of laws coincide (same encoding as the published mission)
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 6.4, p.21 (PDF p.22); proof pp.21–23 (PDF pp.22–24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Intermediary

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 6.4: independent, possibly non-identical bidders; a menu with at most two
prices guarantees `(1/(32 n) - δ) · OPT` against every best response, every `δ > 0`. -/
theorem theorem_6_4 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist)
    (hreg : ∀ i, Regular (D i)) (htail : ∀ i, VanishingTail (D i))
    (hopt : 0 < OPT D) (δ : ℝ) (hδ : 0 < δ) :
    OPT D < ⊤ ∧
    ∃ (a b weight : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hw : weight ∈ Set.Icc 0 1),
      let M := twoPrice a b weight ha hab hw
      (∃ I, BestResponse D M I) ∧
      (((1 / (32 * (n : ℝ)) - δ : ℝ) : EReal) * OPT D) ≤ RandMI D M := by sorry

end LotteryInterm.IID.Supplement

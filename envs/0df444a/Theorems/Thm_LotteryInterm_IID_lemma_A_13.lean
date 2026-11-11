-- Prove2me | Theorems.Thm_LotteryInterm_IID_lemma_A_13
-- name    : LotteryInterm.IID.lemma_A_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:00.758315+00:00
-- url     : https://prove2.me/theorems/1db10879-881b-4ea8-ad9b-8530fac0e274
-- title:
--   Lemma A.13 — deterministic revenue bounds the virtual tail
-- statement:
--   Let $n\ge1$ independent regular bidders satisfy the vanishing-tail condition and $\operatorname{OPT}>0$. For every $t>0$,
--   $$t\Pr[\max_i\phi_i^+(v_i)>t]\le\operatorname{DET},\qquad \phi_i^+=\max\{\phi_i,0\}.$$
--   Here $\operatorname{DET}$ is the supremum of seller revenue guaranteed against every best response to a deterministic posted price. The inequality is the source's tail bound multiplied by its positive threshold.
--
--   It controls the virtual-surplus tail by the deterministic seller benchmark.
--
--   Differences from the source:
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary; reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: probability is bounded by DET divided by t → the positive threshold is cross-multiplied; reason: this avoids extended-real division and specifies the formula domain t greater than zero
--   - encoding: regular distribution with a PDF on its support [a, b]: phi(y) - phi(x) >= 0 for all a <= x <= y <= b (Definition A.2) → ValueDist with density positive on (a, b) and an optional terminal atom; Regular asks phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law, and with f(a) = 0 the source formula gives phi(a) = -infinity, which meets the monotonicity at a; a zero density inside (a, b) would make phi = -infinity at an interior point, which regularity excludes; the two classes of laws coincide
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Lemma A.13, p.41 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

theorem lemma_A_13 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist)
    (hreg : ∀ i, Regular (D i)) (htail : ∀ i, VanishingTail (D i))
    (hopt : 0 < OPT D) (t : ℝ) (ht : 0 < t) :
    ((t * (prior D {v | t < maxVirtual D v}).toReal : ℝ) : EReal) ≤ DET D := by sorry

end LotteryInterm.IID

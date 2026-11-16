-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_4_5
-- name    : LotteryInterm.IID.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:41.732569+00:00
-- url     : https://prove2.me/theorems/5cb5dc3a-9848-4012-b3c0-0459f0e8d13c
-- title:
--   Theorem 4.5 — no uniform approximation for bounded regular laws
-- statement:
--   For every $\varepsilon>0$ there is a bounded regular value law $F$ for a single bidder with
--   $$\mathrm{DET}(F)\ <\ \varepsilon\,\mathrm{OPT}(F),$$
--   and the bound holds under every tie-breaking: for every posted price $p\ge0$, every revenue-maximizing intermediary mechanism and every utility-maximizing option choice of the bidder, the seller earns less than $\varepsilon\,\mathrm{OPT}(F)$. Moreover the witness has $\mathrm{OPT}(F)>0$, and for every posted price the intermediary has a best response, so the inequality is not met by a degenerate law or by an empty set of best responses.
--
--   So without strong regularity, a seller restricted to posted prices can lose almost all of the optimal revenue to a monopolist intermediary; this motivates the randomized menus of §6.
--
--   Differences from the source:
--   - generalization: exists a bounded regular F with DET(F) < eps OPT(F) → the witness also has 0 < OPT and an intermediary best response to every posted price; reason: a stronger conclusion: dropping the two conjuncts gives the source's claim; they rule out witnesses for which OPT = 0 or DET = minus infinity makes the inequality vacuous, and the source assumes OPT > 0 and a best-responding intermediary throughout
--   - generalization: DET(F) < eps OPT(F), proved through Theorem 4.4, whose proof lets the bidder and the intermediary tie-break in favour of the seller → DET(F) < eps OPT(F) for the published worst-case DET, and in addition for every posted price, every intermediary best response and every utility-maximizing option choice the seller earns less than eps OPT(F); reason: a stronger conclusion covering both tie-breaking conventions; dropping the extra conjunct gives the worst-case reading
--   - reading: bounded → F.hi is finite; reason: the support [a, b] has b < infinity
--   - encoding: DET(F), OPT(F) for one distribution → the one-bidder profile fun _ : Fin 1 => F; reason: single-bidder notation
--   - encoding: DET(p), the seller's revenue at posted price p facing a revenue-maximizing intermediary under Assumptions 3.2/3.3 → the published RandMI at postedPrice p (infimum over every intermediary best response, minus infinity if none), and DET the supremum over p >= 0; reason: for a posted price every best response sells access almost surely where the access virtual value is positive, so the infimum is the Assumption 3.2 revenue
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: regular distribution with a PDF on its support [a, b] (Definition A.2 with alpha = 0) → the published ValueDist (density positive on (a, b), optional terminal atom, phi(b) = b) with Regular asking phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law; the two classes of laws coincide (same encoding as the published mission)
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 4.5, p.15 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_GeneralMenu

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 4.5: no uniform approximation for bounded regular laws. The witness has
positive optimal revenue and an intermediary best response to every posted price,
so neither `OPT = 0` nor `DET = ⊥` can make the inequality vacuous; the bound also
holds under every tie-breaking: for every posted price, every intermediary best response
and every utility-maximizing option choice the seller earns less than `ε · OPT`. -/
theorem theorem_4_5 (ε : ℝ) (hε : 0 < ε) :
    ∃ F : ValueDist, F.hi ≠ ⊤ ∧ Regular F ∧ 0 < OPT (fun _ : Fin 1 => F) ∧
      (∀ (p : ℝ) (hp : 0 ≤ p), ∃ I, BestResponse (fun _ : Fin 1 => F) (postedPrice p hp) I) ∧
      DET (fun _ : Fin 1 => F) < (ε : EReal) * OPT (fun _ : Fin 1 => F) ∧
      ∀ (p : ℝ) (hp : 0 ≤ p) (σ : ℝ → ℝ × ℝ),
        IsUtilityMaximizing (GenMenu.ofMenu (postedPrice p hp)) σ →
        ∀ I : Mechanism 1, BestResponse (fun _ : Fin 1 => F) (postedPrice p hp) I →
          ((genSellerRevenue (fun _ : Fin 1 => F) σ I : ℝ) : EReal) <
            (ε : EReal) * OPT (fun _ : Fin 1 => F) := by sorry

end LotteryInterm.IID.Supplement

-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_4_4
-- name    : LotteryInterm.IID.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:09.487782+00:00
-- url     : https://prove2.me/theorems/9a5d5372-d891-496d-ba22-0975d862f504
-- title:
--   Theorem 4.4 — a bounded α-strongly regular law with $\mathrm{DET}=c_\alpha\mathrm{OPT}=c_\alpha\mathrm{APRev}$
-- statement:
--   Consider a single bidder.
--   1. For every $0<\alpha<1$ and every
--   $$H>\max\Big\{\frac{1+\alpha}{\alpha^2},\ \big[(1-\alpha)\alpha^{1+\alpha}\big]^{-1/\alpha}\Big\}$$
--   there is a bounded α-strongly regular value law $F$ whose support ends at the terminal point $H$ such that
--   $$\mathrm{DET}(F)=c_\alpha\,\mathrm{OPT}(F)=c_\alpha\,\mathrm{APRev}(F),$$
--   and no tie-breaking rescues the seller: for every posted price $p\ge0$, every revenue-maximizing intermediary mechanism and every utility-maximizing option choice of the bidder, the seller's revenue is at most $c_\alpha\,\mathrm{OPT}(F)$.
--   2. For $\alpha=1$ and every $H>4$ the same holds with an MHR law ending at $H$ and $c_1=1/e$.
--
--   Here $\mathrm{DET}(F)$ is the best revenue of a seller posting a price against a revenue-maximizing intermediary, with ties resolved against the seller (Assumptions 3.2/3.3). Both equalities are exact. With Theorem 4.2, this shows that $c_\alpha$ cannot be improved for deterministic sellers.
--
--   Differences from the source:
--   - reading: a bounded distribution F_{alpha,H} → a ValueDist F with F.hi = H (terminal point H); reason: the subscript H is the truncation point of the witness in (1) and (2); the Lean witness is the more specific one
--   - encoding: a single bidder → the one-bidder profile fun _ : Fin 1 => F; reason: same auction
--   - generalization: DET(F_{alpha,H}) = c_alpha OPT, with the proof letting the bidder and the intermediary tie-break in favour of the seller → the published DET (worst case over intermediary best responses, lowest-payment bidder choice) equals c_alpha OPT, and in addition for every posted price p, every intermediary best response and every utility-maximizing option choice the seller earns at most c_alpha OPT; reason: a stronger conclusion: the source's DET is attained under either tie-breaking convention, so the statement covers the paper's standing Assumptions 3.2/3.3 and the proof's seller-favourable tie-breaking at once; dropping the extra conjunct gives the worst-case reading
--   - encoding: the two cases (0 < alpha < 1; alpha = 1 and H > 4) → two conjuncts; reason: same statement
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: alpha-strongly regular: phi(y) - phi(x) >= alpha (y - x) for all a <= x <= y <= b (Definition A.2) → StronglyRegular alpha D on the published ValueDist, asked for lo < x <= y <= hi; reason: the same set as the published Regular; the lowest point a is a null type whose density may vanish, and alpha = 0 gives exactly Regular
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 4.4, p.12 (PDF p.13); proof pp.12–14 (PDF pp.13–15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity
import Definitions.Def_LotteryInterm_IID_Supplement_GeneralMenu

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 4.4: tightness of `c_α`. For `0 < α < 1` and `H` above the threshold (or
`α = 1` and `H > 4`) some bounded α-strongly regular law with terminal point `H` gives
a single bidder `DET = c_α · OPT = c_α · APRev`, both equalities exact; moreover no
tie-breaking helps the seller: for every posted price, every intermediary best response
and every utility-maximizing option choice, the seller earns at most `c_α · OPT`. -/
theorem theorem_4_4 :
    (∀ α H : ℝ, 0 < α → α < 1 →
      max ((1 + α) / α ^ 2) (((1 - α) * α ^ (1 + α)) ^ (-1 / α)) < H →
      ∃ F : ValueDist, F.hi = (H : WithTop ℝ) ∧ StronglyRegular α F ∧
        DET (fun _ : Fin 1 => F) = ((cAlpha α : ℝ) : EReal) * OPT (fun _ : Fin 1 => F) ∧
        ((cAlpha α : ℝ) : EReal) * OPT (fun _ : Fin 1 => F) =
          ((cAlpha α : ℝ) : EReal) * APRev (fun _ : Fin 1 => F) ∧
        ∀ (p : ℝ) (hp : 0 ≤ p) (σ : ℝ → ℝ × ℝ),
          IsUtilityMaximizing (GenMenu.ofMenu (postedPrice p hp)) σ →
          ∀ I : Mechanism 1, BestResponse (fun _ : Fin 1 => F) (postedPrice p hp) I →
            ((genSellerRevenue (fun _ : Fin 1 => F) σ I : ℝ) : EReal) ≤
              ((cAlpha α : ℝ) : EReal) * OPT (fun _ : Fin 1 => F)) ∧
    (∀ H : ℝ, 4 < H →
      ∃ F : ValueDist, F.hi = (H : WithTop ℝ) ∧ StronglyRegular 1 F ∧
        DET (fun _ : Fin 1 => F) = ((cAlpha 1 : ℝ) : EReal) * OPT (fun _ : Fin 1 => F) ∧
        ((cAlpha 1 : ℝ) : EReal) * OPT (fun _ : Fin 1 => F) =
          ((cAlpha 1 : ℝ) : EReal) * APRev (fun _ : Fin 1 => F) ∧
        ∀ (p : ℝ) (hp : 0 ≤ p) (σ : ℝ → ℝ × ℝ),
          IsUtilityMaximizing (GenMenu.ofMenu (postedPrice p hp)) σ →
          ∀ I : Mechanism 1, BestResponse (fun _ : Fin 1 => F) (postedPrice p hp) I →
            ((genSellerRevenue (fun _ : Fin 1 => F) σ I : ℝ) : EReal) ≤
              ((cAlpha 1 : ℝ) : EReal) * OPT (fun _ : Fin 1 => F)) := by sorry

end LotteryInterm.IID.Supplement

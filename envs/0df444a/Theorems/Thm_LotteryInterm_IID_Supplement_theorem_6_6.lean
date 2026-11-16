-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_6_6
-- name    : LotteryInterm.IID.Supplement.theorem_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:14:00.373924+00:00
-- url     : https://prove2.me/theorems/382eace6-094e-4c78-9ac2-dcbb892d4c46
-- title:
--   Theorem 6.6 — the $\sqrt\alpha$ bound is tight: $\mathrm{OPT}\ge(\lfloor\min\{n,\alpha^{-1/2}\}\rfloor/10)\cdot\mathrm{SelRev}$
-- statement:
--   For every $n\ge1$ and $0<\alpha\le1$ there are $n$ independent, bounded, α-strongly regular value laws $D_1,\dots,D_n$ with $0<\mathrm{OPT}<\infty$ such that, writing $m=\lfloor\min\{n,\alpha^{-1/2}\}\rfloor$,
--   $$\mathrm{OPT}\ \ge\ \frac m{10}\,\mathrm{SelRev}$$
--   for the seller's revenue $\mathrm{SelRev}$ under **every** seller menu $\mathcal O$ (an arbitrary randomized truthful auction: possibly infinite, with a utility-maximizing option for every type), **every** utility-maximizing option choice $\sigma$ of the forwarded bidder, and **every** best response of the revenue-maximizing intermediary in the message-independent model. Moreover, for these laws every menu has an intermediary best response.
--
--   The paper writes $\mathrm{OPT}/\mathrm{RandMI}=\Omega(\min\{n,\alpha^{-1/2}\})$; the proof gives the factor $m/10$ (for $m\ge10$, $\mathrm{RandMI}\le5/m$ and $\mathrm{OPT}\ge1/2$; for $m<10$, $\mathrm{RandMI}\le\mathrm{OPT}$). With Theorem 6.5 this shows that $\sqrt\alpha$ is the right dependence for many bidders.
--
--   Differences from the source:
--   - generalization: OPT/RandMI = Omega(min{n, alpha^{-1/2}}) with RandMI the seller's maximum revenue over menus → OPT >= (floor(min{n, alpha^{-1/2}})/10) * SelRev for every menu, every utility-maximizing selection and every intermediary best response; reason: the proof's constant m/10; the bound for all menus, tie-breaks and best responses implies the bound on the source's RandMI (the proof's seller-favourable tie-break only increases revenue); since m >= min/2 this gives the Omega
--   - generalization: the intermediary is presumed to best respond → the conclusion also asserts that every menu has a best response; reason: a stronger conclusion; it rules out an upper bound that holds only because no best response exists
--   - encoding: the ratio OPT/RandMI → the product form OPT >= c * SelRev; reason: OPT is positive and finite; the product form is defined when SelRev = 0
--   - encoding: an arbitrary randomized truthful seller auction → GenMenu, a possibly infinite menu containing (0,0) with a utility maximizer for every type; reason: a truthful auction for one bidder is its menu of (allocation, payment) options (Lemma A.12), maximizers being its truthful choices
--   - reading: bounded → (D i).hi finite for every i; reason: each support [a, b] has b < infinity
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: alpha-strongly regular: phi(y) - phi(x) >= alpha (y - x) for all a <= x <= y <= b (Definition A.2) → StronglyRegular alpha D on the published ValueDist, asked for lo < x <= y <= hi; reason: the same set as the published Regular; the lowest point a is a null type whose density may vanish, and alpha = 0 gives exactly Regular
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 6.6, p.26 (PDF p.27); proof pp.26–29 (PDF pp.27–30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity
import Definitions.Def_LotteryInterm_IID_Supplement_GeneralMenu

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 6.6: for every `n ≥ 1` and `0 < α ≤ 1` some `n` independent bounded
α-strongly regular laws have `OPT ≥ (⌊min{n, α^{-1/2}}⌋ / 10) · SelRev` for the
seller's revenue under every (possibly infinite) menu, every utility-maximizing
option choice and every intermediary best response; every menu has a best response. -/
theorem theorem_6_6 (n : ℕ) (hn : 0 < n) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ D : Fin n → ValueDist,
      (∀ i, (D i).hi ≠ ⊤) ∧ (∀ i, StronglyRegular α (D i)) ∧
      0 < OPT D ∧ OPT D < ⊤ ∧
      (∀ O : GenMenu, ∃ I : Mechanism n, GenBestResponse D O I) ∧
      ∀ (O : GenMenu) (σ : ℝ → ℝ × ℝ), IsUtilityMaximizing O σ →
        ∀ I : Mechanism n, GenBestResponse D O I →
          (((⌊min (n : ℝ) (α ^ (-(1 / 2 : ℝ)))⌋₊ : ℝ) / 10 * genSellerRevenue D σ I : ℝ) : EReal)
            ≤ OPT D := by sorry

end LotteryInterm.IID.Supplement

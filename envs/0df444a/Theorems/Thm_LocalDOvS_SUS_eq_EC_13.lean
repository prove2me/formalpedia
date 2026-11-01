-- Prove2me | Theorems.Thm_LocalDOvS_SUS_eq_EC_13
-- name    : LocalDOvS.SUS.eq_EC_13
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:24:22.067981+00:00
-- url     : https://prove2.me/theorems/160b88d1-1a1f-4775-9398-7af3c4b16b5f
-- title:
--   (EC.13), p.ec16 — without a Type-I pair, $f$ varies by at most $M\epsilon/20$ on $S$ (corrected: intermediate bound $2(h_{x^*}+h_{x^{**}})$)
-- statement:
--   Let $S$ be a finite set of decisions with $M=|S|$ points, and for $x\in S$ let $\hat F(x)$ be an empirical mean and $h_x$ a half-width. Suppose
--
--   1. the confidence intervals are correct: $|f(x)-\hat F(x)|\le h_x$ for $x\in S$;
--   2. every half-width is small: $h_x\le |S|\,\epsilon/80$ for $x\in S$;
--   3. there is no Type-I pair: no $x\ne y$ in $S$ with $\hat F(x)+h_x\le\hat F(y)-h_y$.
--
--   Then for all $x,y\in S$,
--   $$
--   |f(x)-f(y)|\le\frac M{20}\,\epsilon .
--   $$
--   In particular this holds for a minimizer $x^*$ and a maximizer $x^{**}$ of $f$ on $S$, which is (EC.13), the hypothesis (EC.7) of Lemma EC.7 in the proof of Theorem 2.
--
--   Differences from the source:
--   - generalization: x*, x** a minimizer and a maximizer of f on S_{k−1} → every pair x, y ∈ S; reason: contains the source's pair
--   - correction: second line ≤ 2(h_{x*}) + h_{x**} ≤ M/20 · ϵ → only the final bound |f(x) − f(y)| ≤ M/20 · ε (the triangle inequality gives 2(h_x + h_y)); reason: the printed intermediate bound is false: f(x*) = 0, F̂(x*) = h, F̂(x**) = 3h − η, f(x**) = 4h − η with h_{x*} = h_{x**} = h satisfy the hypotheses and |f(x*) − f(x**)| = 4h − η > 3h; the printed conclusion M/20 · ϵ holds
--   - encoding: the event and the Type-II condition of the (k−1)-th iteration → explicit hypotheses on f, F̂, h; reason: the lemma is the deterministic step; the event is supplied by good_event and the condition by the algorithm
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, proof of Theorem 2, Case II, eq. (EC.13), p.ec16

import Mathlib

namespace LocalDOvS.SUS

/-- **(EC.13), p.ec16** (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Case II of the proof of
Theorem 2). Let `S` be a finite set of decisions with `M := |S|`, empirical means `F̂(x)` and
half-widths `h_x` for `x ∈ S`. Suppose the confidence intervals are correct,
`|f(x) − F̂(x)| ≤ h_x`, every half-width satisfies `h_x ≤ |S| · ε/80`, and no Type-I pair exists:
there are no `x ≠ y` in `S` with `F̂(x) + h_x ≤ F̂(y) − h_y`. Then
`|f(x) − f(y)| ≤ M/20 · ε` for all `x, y ∈ S`; in particular for a minimizer `x*` and a
maximizer `x**` of `f` on `S`.

**Formalization Note.** The second printed line of (EC.13) reads `2(h_{x*}) + h_{x**}`; the
triangle inequality gives `2(h_{x*} + h_{x**}) ≤ 4 · Mε/80 = M/20 · ε`, which is the printed
conclusion. -/
theorem eq_EC_13 (S : Finset ℕ) (f m hw : ℕ → ℝ) (ε : ℝ)
    (hdev : ∀ x ∈ S, |f x - m x| ≤ hw x)
    (hhw : ∀ x ∈ S, hw x ≤ (S.card : ℝ) * ε / 80)
    (hnoI : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ (m x + hw x ≤ m y - hw y)) :
    ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ (S.card : ℝ) / 20 * ε := by sorry

end LocalDOvS.SUS

-- Prove2me | Theorems.Thm_OptHedgeGames_borwein_erdelyi
-- name    : OptHedgeGames.borwein_erdelyi
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:38:47.912585+00:00
-- url     : https://prove2.me/theorems/86cf6460-b758-4255-a2a9-247b4903958c
-- title:
--   Proof of Lemma 5.2 — the Borwein–Erdélyi inequality for exponential sums
-- statement:
--   Let $n\ge1$, $W>0$ and let $g(u)=\mu_0+\sum_{k=1}^n\mu_ke^{\kappa_ku}$ with arbitrary reals $\mu_0,\mu_k,\kappa_k$. Then
--   $$
--   |g'(0)|\le\frac{2n-1}{W}\max_{|u|\le W}|g(u)|.
--   $$
--   This Bernstein-type inequality has a constant that depends on the number of terms and not on the exponents. It is proved by Borwein and Erdélyi (J. reine angew. Math. 476, 1996), and the paper cites it in the proof of Lemma 5.2.
--
--   Differences from the source:
--   - encoding: max_{|u|≤W} |g(u)| → any bound M with |g(u)| ≤ M on [−W, W]; reason: take M the maximum, which exists by continuity; the statement for every M is equivalent
--   - encoding: the sum runs over k = 1, …, n, W as in the lemma → 1 ≤ n, 0 < W; reason: at n = 0 a nonzero constant g makes the right side negative, so n = 0 is not an instance
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), proof of Lemma 5.2, p.19, citing [BE96]

import Mathlib

namespace OptHedgeGames

/-- **The Borwein–Erdélyi inequality** (Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), proof of Lemma 5.2, p.19, citing P. Borwein and
T. Erdélyi, *A sharp Bernstein-type inequality for exponential sums*, J. reine angew. Math.
476:127–141, 1996). Every real function `g(u) = μ₀ + Σ_{k=1}^n μₖ e^{κₖu}` satisfies
`|g′(0)| ≤ ((2n − 1)/W) max_{|u| ≤ W} |g(u)|`, for every `W > 0`.

**Formalization Note** The maximum is encoded as a bound: for every `M` with `|g(u)| ≤ M` on
`[−W, W]`, the inequality holds with `M`. Taking `M` the maximum, which exists by continuity, gives the
printed inequality. `n ≥ 1`: the sum in the paper runs over `k = 1, …, n`, and at `n = 0` a nonzero
constant `g` makes the right side negative. Coefficients and exponents are arbitrary reals and may
coincide. `2n − 1` is computed in `ℝ`. -/
theorem borwein_erdelyi {n : ℕ} (hn : 1 ≤ n) (μ₀ : ℝ) (μ κ : Fin n → ℝ) (g : ℝ → ℝ)
    (hg : ∀ u, g u = μ₀ + ∑ k, μ k * Real.exp (κ k * u)) (W : ℝ) (hW : 0 < W) (M : ℝ)
    (hM : ∀ u, |u| ≤ W → |g u| ≤ M) :
    |deriv g 0| ≤ (2 * (n : ℝ) - 1) / W * M := by sorry

end OptHedgeGames

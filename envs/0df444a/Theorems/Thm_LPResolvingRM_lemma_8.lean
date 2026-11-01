-- Prove2me | Theorems.Thm_LPResolvingRM_lemma_8
-- name    : LPResolvingRM.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:39:23.216523+00:00
-- url     : https://prove2.me/theorems/91d1b12c-0f58-482c-92aa-a93b71ff21a8
-- title:
--   Lemma 8 — $\ell_1$ concentration of the multinomial distribution
-- statement:
--   Let $\Xi_d=\{q\in\mathbb R^d:\sum_{j=1}^dq_j=1,\ 0<q_j<1\}$. For $q\in\Xi_d$, $t\ge1$ and $\hat q\sim\frac1t\mathrm{Mul}(t,q)$ (the empirical frequencies of $t$ i.i.d. draws from $q$),
--   $$\mathbb P\big(\|\hat q-q\|_1\ge\epsilon\big)\le2^d\exp\Big(-\frac{t\epsilon^2}2\Big)\quad\text{for any }\epsilon>0.$$
--
--   The analysis applies it to the frequencies $n_j(t-1)/(t-1)$ used by the sampled LP.
--
--   **Formalization Note** The constant is $2^d$ on the rendered page (the text layer flattens it to "2d").
--
--   Differences from the source:
--   - encoding: q̂ ∼ (1/t)·Mul(t, q) → the empirical frequencies #{s : ω_s = j}/t of t i.i.d. draws, the probability being the finite sum of ∏_s q_{ω_s} over the draws in the event; reason: the same law
--   - encoding: t implicit (it divides) → t ≥ 1; reason: (1/t)·Mul(t, q) presupposes t ≥ 1
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Lemma 8, p.22 (citing Jaksch et al. 2010, App. C.1)

import Mathlib

open scoped Classical

namespace LPResolvingRM

/-- **Lemma 8 (ℓ₁ concentration of the multinomial distribution)** (arXiv:2101.11092v3, p.22,
citing Jaksch et al. 2010, App. C.1): for `q ∈ Ξ_d = {q ∈ ℝ^d | ∑_j q_j = 1, 0 < q_j < 1}` and
`q̂ ∼ (1/t)·Mul(t, q)`,

`P(‖q̂ − q‖₁ ≥ ϵ) ≤ 2^d exp(−tϵ²/2)` for any `ϵ > 0`.

**Formalization Note.** `q̂` is the vector of empirical frequencies `#{s : ω_s = j}/t` of `t`
i.i.d. draws `ω_1, …, ω_t` from `q` on `Fin d` (the law `(1/t)·Mul(t, q)`), and the probability is
the finite sum of `∏_s q_{ω_s}` over the draws in the event. `t ≥ 1` (it divides). The constant
is `2^d` (rendered page; the text layer flattens it to "2d"). -/
theorem lemma_8 {d : ℕ} (q : Fin d → ℝ) (hq_sum : ∑ j, q j = 1) (hq : ∀ j, 0 < q j ∧ q j < 1)
    (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∑ ω : Fin t → Fin d, (∏ s, q (ω s)) *
        (if ε ≤ ∑ j, |((Finset.univ.filter fun s => ω s = j).card : ℝ) / t - q j| then 1 else 0)
      ≤ 2 ^ d * Real.exp (-(t * ε ^ 2 / 2)) := by sorry

end LPResolvingRM

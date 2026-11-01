-- Prove2me | Theorems.Thm_HomotopyProxVM_lemma_15
-- name    : HomotopyProxVM.lemma_15
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:36:09.812352+00:00
-- url     : https://prove2.me/theorems/d9685be2-fc9e-4321-a92f-b066599e74c3
-- title:
--   Lemma 15, p.24 — the reciprocal recursion
-- statement:
--   Let $M>0$, $q\in(0,1)$, and let $\{\tau_k\}\subset(0,1)$ satisfy $\tau_{k+1}\le\tau_k+Mq^k\tau_k\tau_{k+1}$ for all $k\ge0$. For every $k$ with $1-q-\tau_0M(1-q^k)>0$,
--
--   $$
--   \tau_k\le\frac{\tau_0(1-q)}{1-q-\tau_0M(1-q^k)}
--   \qquad\text{and}\qquad
--   1-\tau_k\ge\frac{(1-\tau_0)(1-q)-\tau_0M+\tau_0Mq^k}{1-q-\tau_0M(1-q^k)} .
--   $$
--
--   The paper uses this to see that $1-\tau_k$ cannot decay faster than the choice (65) allows.
--
--   Differences from the source:
--   - reading: "as long as the denominators are well-defined" → the hypothesis 0 < 1 − q − τ₀M(1 − qᵏ), for the k in question; reason: a zero denominator is undefined, and with a negative one the first bound is negative, hence false since τ_k > 0; positivity is the only reading under which the lemma is true
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Lemma 15, (55), p.24

import Mathlib

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Lemma 15, (55), p.24: for `M > 0`, `q ∈ (0,1)` and `{τ_k} ⊂ (0,1)` with
`τ_{k+1} ≤ τ_k + M qᵏ τ_k τ_{k+1}` for all `k ≥ 0`,
`τ_k ≤ τ₀(1−q)/(1−q−τ₀M(1−qᵏ))` and
`1 − τ_k ≥ ((1−τ₀)(1−q) − τ₀M + τ₀Mqᵏ)/(1−q−τ₀M(1−qᵏ))`,
as long as the denominators are well-defined.

**Formalization Note.** "Well-defined" is read as: the denominator at this `k` is positive. A zero
denominator is undefined, and with a negative one the first bound is negative, hence false, since
`τ_k > 0`. -/
theorem lemma_15 {M q : ℝ} {τ : ℕ → ℝ} (hM : 0 < M) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hτ : ∀ k, τ k ∈ Set.Ioo (0 : ℝ) 1)
    (hrec : ∀ k, τ (k + 1) ≤ τ k + M * q ^ k * τ k * τ (k + 1)) (k : ℕ)
    (hden : 0 < 1 - q - τ 0 * M * (1 - q ^ k)) :
    τ k ≤ τ 0 * (1 - q) / (1 - q - τ 0 * M * (1 - q ^ k)) ∧
    ((1 - τ 0) * (1 - q) - τ 0 * M + τ 0 * M * q ^ k) / (1 - q - τ 0 * M * (1 - q ^ k))
      ≤ 1 - τ k := by sorry

end HomotopyProxVM

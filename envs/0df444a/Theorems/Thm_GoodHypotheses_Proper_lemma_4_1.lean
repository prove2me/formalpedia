-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_lemma_4_1
-- name    : GoodHypotheses.Proper.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:54.448648+00:00
-- url     : https://prove2.me/theorems/f3f2392f-a357-4501-9da3-33e9f839c765
-- title:
--   Lemma 4.1 — the weighted λ-quantile is at most h_mix/(1 − λ)
-- statement:
--   For fixed normalized weights $\tilde W$ (nonnegative, summing to 1), let $\rho$ be the weighted $\lambda$-quantile of the hypotheses $h_1,\dots,h_n$ and $h_{mix}=\sum_i\tilde W_ih_i$ the mixture. Then
--   $$\rho\le\frac1{1-\lambda}\,h_{mix},$$
--   stated for every $\lambda\in[0,1]$ as $(1-\lambda)\rho(x)\le h_{mix}(x)$ at every $x$. With $\lambda=\frac12$ it gives $\rho\le2h_{mix}$, which makes the mixture a reference distribution for importance sampling.
--
--   Differences from the source:
--
--   - encoding: ρ ≤ (1/(1 − λ)) h_mix → (1 − λ)·ρ(x) ≤ h_mix(x) for all x and all λ ∈ [0, 1]; reason: the same inequality for λ < 1; at λ = 1 the printed factor 1/0 is undefined (the paper itself writes (1 − λ)ρ ≤ h_mix, p. 30)
--   - generalization: h_1, …, h_n probability densities → any functions h_i : X → ℝ with h_i ≥ 0 (no measurability, normalization or measure); reason: the inequality is pointwise; probability densities are nonnegative, so it specializes to the paper's statement
--   - encoding: normalized weights W̃ (W̃_i = W_i / ∑_j W_j) → any W with W_i ≥ 0 and ∑_i W_i = 1; reason: the paper uses exactly these properties (p. 21: "any non-negative values summing to one"); normalized MWU weights are such
--   - encoding: items i ∈ [n] = {1, …, n} → i : Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 21, Lemma 4.1

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Proxies

namespace GoodHypotheses.Proper

/-- Lemma 4.1 (p. 21): for normalized weights `W̃` (nonnegative, summing to `1`), nonnegative
hypothesis densities `h_1, …, h_n`, and `λ ∈ [0, 1]`, the weighted `λ`-quantile `ρ` and the
mixture `h_mix = ∑_i W̃_i h_i` satisfy `ρ ≤ (1/(1 − λ)) h_mix`, stated as
`(1 − λ) ρ(x) ≤ h_mix(x)` for every `x`. -/
theorem lemma_4_1 {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ) (lam : ℝ)
    (hh : ∀ i x, 0 ≤ h i x) (hW0 : ∀ i, 0 ≤ W i) (hW1 : ∑ i, W i = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ∀ x, (1 - lam) * quantileProxy h W lam x ≤ mixture h W x := by sorry

end GoodHypotheses.Proper

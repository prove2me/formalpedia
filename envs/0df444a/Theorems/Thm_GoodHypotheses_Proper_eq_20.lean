-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_eq_20
-- name    : GoodHypotheses.Proper.eq_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:56.434206+00:00
-- url     : https://prove2.me/theorems/9c1235bc-2868-40f8-bcb3-79c54966b3c0
-- title:
--   §4.3, Eq. (20) — the weighted median with tie values (1/2 − w₀)/w₁ balances the Scheffé functions: ⟨W̃, S(x)⟩ = 1/2
-- statement:
--   Let $\tilde W$ be normalized weights and $\rho$ the weighted median ($\lambda=\frac12$) of $h_1,\dots,h_n$. At every $x$: $w_0=\sum_i\tilde W_i\mathbf 1\{h_i(x)>\rho(x)\}\le\frac12$, $\sum_i\tilde W_i\mathbf 1\{h_i(x)<\rho(x)\}<\frac12$ and $w_1=\sum_i\tilde W_i\mathbf 1\{h_i(x)=\rho(x)\}>0$. Defining $S_i(x)=1$ if $h_i(x)>\rho(x)$, $0$ if $h_i(x)<\rho(x)$ and $(\frac12-w_0)/w_1$ if $h_i(x)=\rho(x)$, each $S_i$ is a Scheffé function of $(h_i,\rho)$ and
--   $$\langle\tilde W,S(x)\rangle=\sum_i\tilde W_iS_i(x)=\frac12\qquad\text{for all }x\in X,$$
--   so the empirical losses of Eq. (18) satisfy the weighted-sum property $\langle\tilde W,\hat\ell\rangle=0$ (Eq. (21)).
--
--   Differences from the source:
--
--   - generalization: h_1, …, h_n probability densities; the losses ℓ̂^t with reference ν^t → any functions h_i : X → ℝ; the identity ∑_i W_i ℓ̂_i(x, y) = 0 for every real function ν and every pair (x, y); reason: all clauses are pointwise; the paper's densities and its ν^t are instances
--   - reading: "ρ^t and ℓ̂^t_i satisfy the weighted-sum property" → ∑_i W_i ℓ̂_i(x, y) = 0 for all x, y (Eq. (21)); reason: the passage derives the property as Eq. (21), ⟨W̃^t, ℓ̂^t⟩ = 0
--   - encoding: normalized weights W̃ (W̃_i = W_i / ∑_j W_j) → any W with W_i ≥ 0 and ∑_i W_i = 1; reason: the paper uses exactly these properties (p. 21: "any non-negative values summing to one"); normalized MWU weights are such
--   - encoding: items i ∈ [n] = {1, …, n} → i : Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), pp. 19–20, §4.3, Eq. (20)

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Proxies

namespace GoodHypotheses.Proper

/-- §4.3, Eq. (20) (pp. 19–20): for normalized weights `W̃` (nonnegative, summing to `1`) and the
weighted median `ρ` of `h_1, …, h_n`, at every `x`: `w₀(x) = ∑_i W̃_i 1{h_i(x) > ρ(x)} ≤ 1/2`,
`∑_i W̃_i 1{h_i(x) < ρ(x)} < 1/2`, `w₁(x) = ∑_i W̃_i 1{h_i(x) = ρ(x)} > 0`; the functions
`S_i` equal to `1` above `ρ`, `0` below and `(1/2 − w₀)/w₁` at ties are Scheffé functions of
`(h_i, ρ)`; `⟨W̃, S(x)⟩ = ∑_i W̃_i S_i(x) = 1/2`; and consequently the empirical losses of
Eq. (18) built from these `S_i`, `ρ` and any reference density `ν` satisfy the weighted-sum
property `⟨W̃, ℓ̂⟩ = 0` (Eq. (21)) at every pair of sample points `(x, y)`. -/
theorem eq_20 {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ)
    (hW0 : ∀ i, 0 ≤ W i) (hW1 : ∑ i, W i = 1) :
    (∀ x, weightAbove h W x ≤ 1 / 2 ∧ weightBelow h W x < 1 / 2 ∧ 0 < weightTie h W x) ∧
      (∀ i, IsScheffe (h i) (medianProxy h W) (medianScheffe h W i)) ∧
      (∀ x, ∑ i, W i * medianScheffe h W i x = 1 / 2) ∧
      (∀ (ν : X → ℝ) (x y : X),
        ∑ i, W i * empiricalLoss (medianScheffe h W i) (medianProxy h W) ν x y = 0) := by sorry

end GoodHypotheses.Proper

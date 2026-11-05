-- Prove2me | Theorems.Thm_MenuCostPricing_lemma_3_2
-- name    : MenuCostPricing.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:04.093192+00:00
-- url     : https://prove2.me/theorems/e38b6a3c-43f6-4553-b017-8c16cab849b5
-- title:
--   Lemma 3.2 — a list of $O((nL/\delta)^{O(T)})$ weight guesses contains one satisfying (5)
-- statement:
--   There are universal constants $K>0$ and $c\ge0$ such that the following holds for every instance and every $\delta>0$. The program `weightGuesses` (the construction of Appendix B.1) returns a list of vectors $(\hat w_1,\dots,\hat w_T)$ such that for **every** pricing strategy $x$ some vector in the list satisfies
--   $$
--   w_t(x)\le\hat w_t\le(1+\delta)\,w_t(x)\qquad\text{for all }t\in[T],\qquad(5)
--   $$
--   and the program executes at most $K\,(1+nL\max(1,1/\delta))^{c(T+1)}$ unit operations.
--
--   The guesses let the FPTAS replace the total weight $w_t(x^*)$ of the unknown optimum by a known estimate.
--
--   Differences from the source:
--   - generalization: a vector satisfying (5) for the optimum x∗ → for every strategy x a vector satisfying (5) for x; reason: App. B.1 uses only that x∗ is a strategy; specializes at x = x∗
--   - generalization: δ = ϵ/(8ϱmax) → every δ > 0; reason: the construction works for every δ > 0; specializes at δ = ϵ/(8ϱmax) and at the program's δ = min(ϵ,1)/(8ϱmax)
--   - reading: "we can construct in O((nL/δ)^{O(T)}) time a set of weight vectors" → the explicit charged program weightGuesses executes at most K·(1 + nL·max(1, 1/δ))^{c(T+1)} unit operations, K and c universal and quantified before every type; reason: O(·) exponents as universal constants; the base 1 + nL·max(1, 1/δ) ≥ 2 and the exponent T + 1 make the bound meaningful at n = L = δ = 1 (writing T coordinates costs T), at T = 0 and for large δ; for δ ≤ 1 the base is 1 + nL/δ
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Lemma 3.2, p.15; proof App. B.1, p.46

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Lemma 3.2, p.15 (proof App. B.1, p.46): "We can
construct in O((nL/δ)^{O(T)}) time a set of weight vectors that contains at least one vector
(ŵ₁, …, ŵ_T) satisfying inequality (5), simultaneously for all t ∈ [T]", where (5) is
`wₜ(x∗) ≤ ŵₜ ≤ (1 + δ)·wₜ(x∗)`.

There are universal constants `K > 0`, `c ≥ 0` such that for every instance, every `δ > 0` and
every pricing strategy `x`, the list returned by `weightGuesses` contains a vector `ŵ` (of length
`T`) with `wₜ(x) ≤ ŵₜ ≤ (1 + δ)·wₜ(x)` for all `t`, and `weightGuesses` executes at most
`K·(1 + nL·max(1, 1/δ))^{c(T+1)}` unit operations.

**Formalization Note.** Stated for every strategy `x` (the optimum `x∗` is one). `O(·)` exponents
are universal constants quantified before every type; the base `1 + nL·max(1, 1/δ) ≥ 2` and the
exponent `T + 1` make the bound meaningful at `n = L = δ = 1` and `T = 0`. For `δ ≤ 1` the base is
`1 + nL/δ`; the `max` keeps it `≥ 2` for large `δ`, where `(nL/δ)^{O(T)}` would drop below the `T`
steps of writing a vector. -/
theorem lemma_3_2 :
    ∃ K c : ℝ, 0 < K ∧ 0 ≤ c ∧
      ∀ {n L T : ℕ} (I : Instance n L T), I.Standing → ∀ δ : ℝ, 0 < δ →
        (∀ x : Strategy n L T, ∃ g ∈ ((I.weightGuesses δ).run 0).1, g.size = T ∧
          ∀ t : Fin T, I.wt x t ≤ g[t.val]! ∧ g[t.val]! ≤ (1 + δ) * I.wt x t) ∧
        ((((I.weightGuesses δ).run 0).2 : ℕ) : ℝ) ≤
          K * (1 + (n : ℝ) * L * max 1 (1 / δ)) ^ (c * ((T : ℝ) + 1)) := by sorry

end MenuCostPricing

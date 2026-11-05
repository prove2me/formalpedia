-- Prove2me | Theorems.Thm_MenuCostPricing_eq_19
-- name    : MenuCostPricing.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:55.556897+00:00
-- url     : https://prove2.me/theorems/99a02de2-1748-41b1-9986-f212cad29caa
-- title:
--   (19) — the evaluator computes $\hat{\mathcal R}^i_{\alpha,\beta}(x_i)$ (corrected: count $O(T\,\sigma_{\max}((u^1_i)^3+L_\nu))$, not $O(T(u^1_i)^3\sigma_{\max})$)
-- statement:
--   There is a universal constant $K>0$ such that, for every instance, every guess vector $\hat w\ge0$, every $\beta\ge0$, every product $i$ and every single-product price vector $x_i$, the program `evalReward`, which fills the table
--   $$
--   \hat{\mathcal R}(t,u)=\sum_{\nu\in S_t}\Pr[N_t=\nu]\sum_{d\le\nu}\Pr\big[\hat D^t_i=d\mid N_t=\nu\big]\Big(\min\{d,u\}\,p_{i,x^t_i}+\hat{\mathcal R}(t+1,[u-d]^+)\Big),\qquad \hat{\mathcal R}(T+1,\cdot)=0,
--   $$
--   for $u=0,\dots,u^1_i$ with $[\hat D^t_i\mid N_t=\nu]\sim\mathrm{Binomial}(\nu,\hat q)$, returns exactly $\hat{\mathcal R}^i_{\alpha,\beta}(x_i)=\hat{\mathcal R}(1,u^1_i)$, and executes at most
--   $$
--   K\,(T+1)\,(\sigma_{\max}+1)\,\big((u^1_i+1)^3+L_\nu\big)
--   $$
--   unit operations, where $\sigma_{\max}$ is the largest support size and $L_\nu$ the largest bit length of a support point.
--
--   The evaluator is what lets the dynamic program update its reward-to-go exactly.
--
--   Differences from the source:
--   - correction: running time O(T·(u¹ᵢ)³·σmax) → K·(T + 1)·(σmax + 1)·((u¹ᵢ + 1)³ + Lν), Lν the largest bit length of a support point; reason: the printed count is false for support points given in binary: with T = n = L = 1, u¹ = 1 and N₁ ≡ 2^m (all assumptions of §1.1 hold), R̂¹ = p·(1 − (1 − q̂)^{2^m}) is a polynomial of degree 2^m in q̂, and a program of k arithmetic operations computes a rational function of degree ≤ 2^k, so k ≥ m while the printed count is O(1) on this family; the added Lν term is attained by square and multiply; the offsets T + 1, σmax + 1, u¹ᵢ + 1 keep the bound positive at T = 0 and u¹ᵢ = 0, where the printed expression is 0
--   - encoding: Sₜ = {ν : Pr[Nₜ = ν] > 0} and σmax its largest size → the listed support, which may contain points of mass 0, and σmax the longest list; reason: the list is the input; a list of positive-mass points is Sₜ and gives the printed σmax
--   - reading: "a total of O(|Sₜ|·u²) basic operations" for (19) → the explicit charged program evalReward; masses for d < min(u, ν + 1) by one square-and-multiply power and incremental products, the tail d ≥ u as one term; reason: the paper does not fix the cost model or the procedure; unit-cost arithmetic, powers charged per multiplication
--   - encoding: Dᵗᵢ(x) = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν), each customer making an MNL choice; Nₜ independent across periods; D̂ᵗᵢ a sum of Nₜ i.i.d. Bernoulli(q̂) variables → demandLaw: per period, Nₜ from the listed masses, then Nₜ i.i.d. categorical choices on Option (Fin n) counted per product, periods independent (Measure.pi); proxyPathLaw: per product, Nₜ then a sum of Nₜ i.i.d. Bernoulli, periods independent; reason: the paper's joint model written as PMFs; R and R̂ are the printed sums of expectations under these laws
--   - encoding: Ŷᵗᵢ(xᵢ, ν; β) ∼ Bernoulli(wᵗ_{i,xᵢ}/(1 + (1 + β)ŵₜ)) → Bernoulli with parameter clamped to [0, 1] (bern); reason: for a strategy feasible to APX(α, β) under Standing the parameter lies in [0, 1], so the clamp changes no instance the paper considers; it makes R̂ⁱ defined for every single-product strategy, which §3.6 evaluates
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), App. B.6, equation (19) and "From a running time perspective", pp.51–52

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), App. B.6, equation (19), pp.51–52 (**corrected**
operation count): the dynamic program
`R̂(t, u) = Σ_{ν∈Sₜ} Pr[Nₜ = ν]·Σ_{d≤ν} Pr[D̂ᵗᵢ(xᵢ; β) = d | Nₜ = ν]·(min{d, u}·Σ_ℓ p_{iℓ}xᵗ_{iℓ} + R̂(t + 1, [u − d]⁺))`
with `R̂(T + 1, ·) = 0` computes `R̂ⁱ_{α,β}(xᵢ) = R̂(1, u¹ᵢ)` exactly, and the paper bounds its running time
by `O(T·(u¹ᵢ)³·σmax)`.

There is a universal constant `K > 0` such that for every instance, every guess vector `ŵ ≥ 0`, every
`β ≥ 0`, every product `i` and every single-product price vector `xᵢ`, the program `evalReward`
returns `R̂ⁱ_{α,β}(xᵢ)` and executes at most `K·(T + 1)·(σmax + 1)·((u¹ᵢ + 1)³ + Lν)` unit operations,
where `σmax` is the largest support size and `Lν` the largest bit length of a support point.

**Formalization Note.** The printed count `O(T·(u¹ᵢ)³·σmax)` is false when the support points are given
in binary: with `T = n = L = 1`, `u¹ = 1` and `N₁ ≡ 2^m`, `R̂¹ = p·(1 − (1 − q̂)^{2^m})`, a polynomial of degree
`2^m` in `q̂`, which no program of fewer than `m` arithmetic operations computes; the printed count is
`O(1)` on this family. The added `Lν` term (bit length, not magnitude, of the support) is attained by
square and multiply. `(T + 1)`, `(σmax + 1)` and `(u¹ᵢ + 1)` keep the bound positive at `T = 0` and
`u¹ᵢ = 0`. -/
theorem eq_19 :
    ∃ K : ℝ, 0 < K ∧
      ∀ {n L T : ℕ} (I : Instance n L T), I.Standing → ∀ (ŵ : Fin T → ℝ) (β : ℝ),
        (∀ t, 0 ≤ ŵ t) → 0 ≤ β → ∀ (i : Fin n) (xi : Fin T → Fin L),
          ((I.evalReward (Array.ofFn ŵ) β i.val (Array.ofFn fun t => (xi t).val)).run 0).1 =
              I.Rhati ŵ β i xi ∧
            ((((I.evalReward (Array.ofFn ŵ) β i.val (Array.ofFn fun t => (xi t).val)).run 0).2 : ℕ) :
                ℝ) ≤
              K * ((T : ℝ) + 1) * ((I.sigmaMax : ℝ) + 1) *
                (((I.u i : ℝ) + 1) ^ 3 + I.bitMax) := by sorry

end MenuCostPricing

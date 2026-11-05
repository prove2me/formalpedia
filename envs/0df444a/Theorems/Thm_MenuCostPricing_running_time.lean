-- Prove2me | Theorems.Thm_MenuCostPricing_running_time
-- name    : MenuCostPricing.running_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:17.431585+00:00
-- url     : https://prove2.me/theorems/92bea8f3-8961-40f7-96ae-703ecfb03b9e
-- title:
--   §3.7 "Overall running time" — the program executes $O((nL\varrho_{\max}/\epsilon)^{O(T)}\cdot(|I|\,\|U^1\|_\infty)^{O(1)})$ operations
-- statement:
--   There are universal constants $K>0$ and $c\ge0$ such that for every instance and every $\epsilon>0$ the program `fptas` executes at most
--   $$
--   K\cdot\big(2nL\,\varrho_{\max}\max(1,1/\epsilon)\big)^{c(T+1)}\cdot\big((T+1)(\sigma_{\max}+1)(\|U^1\|_\infty+1)(L_\nu+1)\big)^c
--   $$
--   unit operations, where $\sigma_{\max}$ is the largest support size and $L_\nu$ the largest bit length of a support point. This covers the dynamic program, the guessing of Step 1 and the construction of the grids.
--
--   On rational instances each of $T+1$, $\sigma_{\max}+1$, $L_\nu+1$ is at most $|I|$, which gives the bound of Theorem 3.1.
--
--   Differences from the source:
--   - generalization: |I| (the input size in binary) in O((nL/ϵ·ϱmax)^{O(T)}·(|I|·‖U¹‖∞)^{O(1)}) → (T + 1)(σmax + 1)(Lν + 1), stated for real data; reason: a real instance has no binary size; these are the parts of |I| the loops depend on, each ≤ |I| on rational instances, so the bound implies the printed one
--   - encoding: Sₜ = {ν : Pr[Nₜ = ν] > 0} and σmax its largest size → the listed support, which may contain points of mass 0, and σmax the longest list; reason: the list is the input; a list of positive-mass points is Sₜ and gives the printed σmax
--   - reading: O(·) exponents and the accuracy ϵ → universal constants K, c quantified before every type; base 2nLϱmax·max(1, 1/ϵ) ≥ 2 with exponent c(T + 1); the program runs with min(ϵ, 1); reason: the 2^{T−1} guesses of Γ must be paid for even at n = L = ϱmax = 1; T + 1 covers T = 0; max(1, 1/ϵ) because no program can meet (1/ϵ)^{cT} as ϵ → ∞
--   - reading: "basic operations" → unit operations of the instrumented program fptas (Work monad), powers charged per multiplication, no logarithms; reason: the paper does not fix the cost model; this is the real RAM with unit-cost arithmetic
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.7, "Overall running time", pp.21–22

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), §3.7 "Overall running time", pp.21–22: "Hence,
recalling that δ = ϵ/8·1/ϱmax, computing the pricing strategy x̂ requires
O((nL/ϵ·ϱmax)^{O(T)}·(|I|·‖U¹‖∞)^{O(1)}) basic operations", and, "after accounting for the guessing
procedure in Step 1 and the construction of Dω and Dρ in Step 4", the whole program.

There are universal constants `K > 0`, `c ≥ 0` such that for every instance and every `ε > 0` the
program `fptas` executes at most
`K·(2nL·ϱmax·max(1, 1/ε))^{c(T+1)}·((T + 1)(σmax + 1)(‖U¹‖∞ + 1)(Lν + 1))^c` unit operations, where
`σmax` is the largest support size and `Lν` the largest bit length of a support point.

**Formalization Note.** Stated for real data: `(T + 1)(σmax + 1)(Lν + 1)` stands for the `|I|` factor
(the parts of the input size the evaluator (19) and the support loops depend on), which a real instance
does not have. `O(·)` exponents are universal constants quantified before every type; the factor `2`
and the exponent `T + 1` keep the base `≥ 2` (the `2^{T−1}` guesses of `Γ` must be paid for even at
`n = L = ϱmax = 1`). -/
theorem running_time :
    ∃ K c : ℝ, 0 < K ∧ 0 ≤ c ∧
      ∀ {n L T : ℕ} (I : Instance n L T), I.Standing → ∀ ε : ℝ, 0 < ε →
        ((I.ops ε : ℕ) : ℝ) ≤
          K * (2 * (n : ℝ) * L * I.rhoMax * max 1 (1 / ε)) ^ (c * ((T : ℝ) + 1)) *
            (((T : ℝ) + 1) * ((I.sigmaMax : ℝ) + 1) * ((I.uMax : ℝ) + 1) * ((I.bitMax : ℝ) + 1)) ^ c
          := by sorry

end MenuCostPricing

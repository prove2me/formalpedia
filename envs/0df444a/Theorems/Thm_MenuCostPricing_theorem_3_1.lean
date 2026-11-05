-- Prove2me | Theorems.Thm_MenuCostPricing_theorem_3_1
-- name    : MenuCostPricing.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:21.017634+00:00
-- url     : https://prove2.me/theorems/abfec511-a656-463f-8eb8-cca96ed3ce03
-- title:
--   Theorem 3.1 — a budget-feasible $(1-\epsilon)$-optimal pricing strategy in time $O((|I|/\epsilon\cdot\varrho_{\max})^{O(T)}\cdot\|U^1\|_\infty^{O(1)})$
-- statement:
--   There are universal constants $K>0$ and $c\ge0$ such that for every instance of dynamic pricing with menu costs and every accuracy level $\epsilon>0$, the algorithm `fptas` of the mission satisfies:
--   1. if some pricing strategy is budget-feasible, the algorithm returns a strategy;
--   2. any strategy $\hat x$ it returns is budget-feasible and
--   $$
--   R(\hat x)\ge(1-\epsilon)\cdot R(x)\qquad\text{for every budget-feasible }x,
--   $$
--   i.e. it is within factor $1-\epsilon$ of optimal;
--   3. on every rational instance, the algorithm executes at most
--   $$
--   K\cdot\big(|I|\cdot\varrho_{\max}\cdot\max(1,1/\epsilon)\big)^{c(T+1)}\cdot\max(1,\|U^1\|_\infty)^{c}
--   $$
--   unit operations, where $|I|$ is the input size in binary and $\varrho_{\max}=\max_i p^i_{\max}/p^i_{\min}$.
--
--   This is an FPTAS when $\varrho_{\max}$ and $\|U^1\|_\infty$ are polynomial in $|I|$ and $1/\epsilon$ and $T=O(1)$, the regime the paper argues fits grocery retail.
--
--   Differences from the source:
--   - reading: "our algorithm" → the explicit instrumented program fptas (guesses, evaluator (19), table of (9)–(10), ρ̂ (11), traceback); reason: without a program, clause 2 holds by taking the optimum (the strategy set is finite)
--   - reading: "after accounting for the guessing procedure" (§3.7) → the program returns, among the candidates of all guesses, one with the largest proxy reward R̂_{2δ,δ}(x̂) (first on ties); reason: the paper does not say how the guess is chosen; every candidate is feasible (Lemma 3.5 for every guess), so this selection keeps the guarantee
--   - reading: the update ρ − Dρ(R̂ⁱ_{2δ,δ}(xᵢ)) in (9), which may be negative and then is not in Dρ → the reward index is updated by truncated subtraction, i.e. clamped at 0; reason: the paper leaves the case implicit; the base case (10) only asks ρ ≤ 0, so the clamp changes no value its proofs use
--   - reading: running time in "basic operations" with O(T) and O(1) exponents → unit operations of the Work monad; universal K, c quantified before every type; base |I|·ϱmax·max(1, 1/ϵ), exponent c(T + 1), max(1, ‖U¹‖∞); reason: no cost model or constants are printed; T + 1 and max(1, ‖U¹‖∞) cover T = 0 and zero inventory; max(1, 1/ϵ) because no program meets (1/ϵ)^{cT} as ϵ → ∞
--   - encoding: δ = ϵ/(8ϱmax) → the program uses δ = min(ϵ, 1)/(8ϱmax); reason: equal for ϵ ≤ 1; for ϵ > 1 the accuracy clause with ϵ still holds and APX(2δ, δ) stays formulated with α, β ∈ [0, 1]
--   - encoding: "within factor 1 − ϵ of optimal" → R(x̂) ≥ (1 − ϵ)·R(x) for every budget-feasible x, and a strategy is returned whenever one is budget-feasible; reason: the same statement without naming an optimum; the paper presumes DPMC feasible
--   - generalization: instances given in binary → accuracy (clauses 1–2) for real data; the time bound for rational instances; reason: rational instances are real instances; the time bound needs a finite representation
--   - encoding: Dᵗᵢ(x) = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν), each customer making an MNL choice; Nₜ independent across periods; D̂ᵗᵢ a sum of Nₜ i.i.d. Bernoulli(q̂) variables → demandLaw: per period, Nₜ from the listed masses, then Nₜ i.i.d. categorical choices on Option (Fin n) counted per product, periods independent (Measure.pi); proxyPathLaw: per product, Nₜ then a sum of Nₜ i.i.d. Bernoulli, periods independent; reason: the paper's joint model written as PMFs; R and R̂ are the printed sums of expectations under these laws
--   - encoding: Ŷᵗᵢ(xᵢ, ν; β) ∼ Bernoulli(wᵗ_{i,xᵢ}/(1 + (1 + β)ŵₜ)) → Bernoulli with parameter clamped to [0, 1] (bern); reason: for a strategy feasible to APX(α, β) under Standing the parameter lies in [0, 1], so the clamp changes no instance the paper considers; it makes R̂ⁱ defined for every single-product strategy, which §3.6 evaluates
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Theorem 3.1, p.14

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm
import Definitions.Def_MenuCostPricing_Rational

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Theorem 3.1, p.14: "For any accuracy level ϵ > 0,
dynamic pricing with menu costs can be approximated within factor 1 − ϵ of optimal. The running time of
our algorithm is O((|I|/ϵ·ϱmax)^{O(T)}·‖U¹‖∞^{O(1)})."

There are universal constants `K > 0` and `c ≥ 0` such that, for every instance and every `ε > 0`:
1. if a budget-feasible pricing strategy exists, the program `fptas` returns a strategy;
2. whatever it returns is budget-feasible and has expected revenue at least `(1 − ε)·R(x)` for every
   budget-feasible `x`;
3. on rational instances it executes at most `K·(|I|·ϱmax·max(1, 1/ε))^{c(T+1)}·max(1, ‖U¹‖∞)^c` unit
   operations, `|I|` being the input size in binary.

**Formalization Note.** The statement is about the explicit program `Instance.fptas` ("our algorithm");
without it, clause 2 would hold by taking the optimum. Accuracy holds for real data; the running time
needs a finite representation, hence rational data. `O(·)` exponents are universal constants quantified
before every type; `T + 1` and `max(1, ‖U¹‖∞)` keep the bound meaningful at `T = 0` and zero inventory,
and `max(1, 1/ε)` for `ε > 1`. -/
theorem theorem_3_1 :
    ∃ K c : ℝ, 0 < K ∧ 0 ≤ c ∧
      (∀ {n L T : ℕ} (I : Instance n L T), I.Standing → ∀ ε : ℝ, 0 < ε →
        ((∃ x, I.Feasible x) → ∃ xh, I.output ε = some xh) ∧
        (∀ xh, I.output ε = some xh →
          I.Feasible xh ∧ ∀ x, I.Feasible x → (1 - ε) * I.R x ≤ I.R xh)) ∧
      (∀ {n L T : ℕ} (J : RatInstance n L T), J.toReal.Standing → ∀ ε : ℝ, 0 < ε →
        ((J.toReal.ops ε : ℕ) : ℝ) ≤
          K * ((J.inputSize : ℝ) * J.toReal.rhoMax * max 1 (1 / ε)) ^ (c * ((T : ℝ) + 1)) *
            (max 1 (J.toReal.uMax : ℝ)) ^ c) := by sorry

end MenuCostPricing

-- Prove2me | Theorems.Thm_NonlinearPriority_corollary_A1
-- name    : NonlinearPriority.corollary_A1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:20.177867+00:00
-- url     : https://prove2.me/theorems/d6467589-3e3f-43b2-bf4a-a6c24c106d1d
-- title:
--   Corollary A.1, p.18 — the index $I(\gamma)$ ranks the costs of $\pi_k,\pi_{k+1},\bar\pi_k$
-- statement:
--   Under the hypotheses of Proposition 2, let $I(\bar\pi_k)=0$ and, for $i,j\in\{k,k+1\}$, $j\ne i$,
--   $$I(\pi_i)=\frac{\delta^{\pi_i}_i\mu_i-\delta^{\pi_i}_j\mu_j}{\bar\rho_{k-1}-\rho_i}.$$
--   Then for any two policies $\gamma,\gamma'\in\{\pi_k,\pi_{k+1},\bar\pi_k\}$,
--   $$I(\gamma)\ge I(\gamma')\iff C^\gamma\le C^{\gamma'}.$$
--   In particular the policy with the largest (smallest) value of $I$ has the lowest (highest) long-run average cost among the three.
--
--   Only the two indices $\delta^{\gamma}_i=\delta^{\gamma,\bar\pi_k}_i$, $\gamma\in\{\pi_k,\pi_{k+1}\}$, are needed to rank the three policies.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - reading: C^π ≡ lim_{t→∞} Σ_i Σ_{k ≤ n_i(t)} C_i(V^{π,x0}_{i,k})/t (1), a random limit with x0 only in the notation → IsLongRunAvgCost: the constant c such that, for every initial state x0, the average converges to c almost surely; reason: the strongest reading; §A.2.1 proves it from every initial state
--   - generalization: each C_i differentiable and nondecreasing (p. 3) → each C_i an arbitrary measurable function, subject to Assumption 1; reason: only the integrability of C_i(W) is used; differentiable functions are measurable, so every instance of the paper is included
--   - encoding: service times with nth moments τ(n)_i > 0, finiteness not stated → finite second moments ∫ x² dS_i < ∞ for every type; reason: without them the means in (3)–(4) are ∞ − ∞ and the statement is undefined; this only excludes such instances
--   - encoding: types 1, …, K, pair (k, k+1) with k ∈ {1, …, K−1}; ρ̄_{k−1}, ρ̄_{k+1}, Σ_{ℓ=1}^{k−1}, Σ_{ℓ=1}^{k+1} → Fin K (0-based), pair of types k, k+1 with k+1 < K; rhoBar k, rhoBar (k+2), sumP2 k, sumP2 (k+2); reason: index shift only: the paper's k is k+1 here, and rhoBar m is the paper's ρ̄_m
--   - reading: 'without loss of generality, type i customers have priority order i under policy π' (p. 4) → π_k gives type i order i; π_{k+1} swaps the orders of k and k+1; π̄_k gives k and k+1 one common order and keeps the order of all other types; reason: the setting of every displayed formula of the paper (ρ̄_{k−1}, ρ̄_{k+1}, (A.8)–(A.10))
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
--   - generalization: 'the policy with the largest (smallest) value of I(γ) … has the lowest (highest) long-run average cost' → for every two of the three policies, I(γ) ≥ I(γ') ↔ C^γ ≤ C^{γ'}; reason: the order equivalence the proof establishes; it implies the printed statement, including its reading under ties
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, Corollary A.1, p.18 (PDF 19)

import Mathlib
import Definitions.Def_NonlinearPriority_IsLongRunAvgCost
import Definitions.Def_NonlinearPriority_indexI

open MeasureTheory

namespace NonlinearPriority

/-- **Corollary A.1: ranking the three policies by the index `I`** (p. 18, PDF 19). Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

"Let I(π̄k) ≡ 0 and I(πi) ≡ (δ^{πi}_i μi − δ^{πi}_j μj)/(ρ̄k−1 − ρi) for i, j ∈ {k, k + 1} and j ≠ i.
Then, the policy with the largest (smallest) value of I(γ) for γ ∈ {πk, πk+1, π̄k} has the lowest
(highest) long-run average cost among these three policies."

Indexing the three policies `π_k, π_{k+1}, π̄_k` by `0, 1, 2`, for every two of them `γ, γ'`:
`I(γ) ≥ I(γ')` if and only if `C^γ ≤ C^{γ'}`. Hence the largest `I` has the lowest cost and the
smallest `I` the highest. -/
theorem corollary_A1 {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr)
    (hS2 : ∀ l, Integrable (fun x => x ^ 2) (P.S l))
    (C : Fin K → ℝ → ℝ) (hC : ∀ i, Measurable (C i))
    (k : ℕ) (a b : Fin K) (ha : (a : ℕ) = k) (hb : (b : ℕ) = k + 1)
    (w : (Fin K → ℕ) → Fin K → ProbabilityMeasure ℝ)
    (hw : ∀ γ ∈ ({piK k, piK1 k, piBar k} : Set (Fin K → ℕ)), ∀ i, IsSteadyStateLaw X γ i (w γ i))
    (hA1 : ∀ γ ∈ ({piK k, piK1 k, piBar k} : Set (Fin K → ℕ)), ∀ i,
      Integrable (C i) (w γ i : Measure ℝ))
    (cK cK1 cBar : ℝ) (hcK : IsLongRunAvgCost X C (piK k) cK)
    (hcK1 : IsLongRunAvgCost X C (piK1 k) cK1) (hcBar : IsLongRunAvgCost X C (piBar k) cBar) :
    ∀ u v : Fin 3,
      (![indexI P C w k a b, indexI P C w k b a, 0] u ≥ ![indexI P C w k a b, indexI P C w k b a, 0] v
        ↔ ![cK, cK1, cBar] u ≤ ![cK, cK1, cBar] v) := by sorry

end NonlinearPriority

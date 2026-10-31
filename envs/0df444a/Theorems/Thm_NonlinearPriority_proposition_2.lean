-- Prove2me | Theorems.Thm_NonlinearPriority_proposition_2
-- name    : NonlinearPriority.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:42.034967+00:00
-- url     : https://prove2.me/theorems/7edab9f0-202e-4246-8760-2701f24c7483
-- title:
--   Proposition 2, p.5 — the comparison of $\pi_k,\pi_{k+1},\bar\pi_k$ is a $c\mu$-rule in $\delta$
-- statement:
--   Fix adjacent types $k,k+1$ and suppose Assumption 1 holds under $\pi_k$, $\pi_{k+1}$ and $\bar\pi_k$: $\mathbb E[|C_i(W^\gamma_i)|]<\infty$ for every type $i$ and these three policies. Let $\delta^{\gamma_1,\gamma_2}_i$ be defined by (3). Then
--
--   1. $C^{\pi_k}\le C^{\bar\pi_k}$ if and only if $\delta^{\pi_k,\bar\pi_k}_k\mu_k\ge\delta^{\pi_k,\bar\pi_k}_{k+1}\mu_{k+1}$;
--   2. $C^{\pi_{k+1}}\le C^{\bar\pi_k}$ if and only if $\delta^{\pi_{k+1},\bar\pi_k}_{k+1}\mu_{k+1}\ge\delta^{\pi_{k+1},\bar\pi_k}_k\mu_k$;
--   3. $C^{\pi_k}\le C^{\pi_{k+1}}$ if and only if $\delta^{\pi_k,\pi_{k+1}}_k\mu_k\ge\delta^{\pi_k,\pi_{k+1}}_{k+1}\mu_{k+1}$.
--
--   Here $C^\gamma$ is the long-run average cost (1) and service times have finite second moments. With linear costs $\delta_i=c_i$ and this is the classical $c\mu$-rule; in general $\delta$ plays the role of a marginal cost.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - reading: C^π ≡ lim_{t→∞} Σ_i Σ_{k ≤ n_i(t)} C_i(V^{π,x0}_{i,k})/t (1), a random limit with x0 only in the notation → IsLongRunAvgCost: the constant c such that, for every initial state x0, the average converges to c almost surely; reason: the strongest reading; §A.2.1 proves it from every initial state
--   - generalization: each C_i differentiable and nondecreasing (p. 3) → each C_i an arbitrary measurable function, subject to Assumption 1; reason: only the integrability of C_i(W) is used; differentiable functions are measurable, so every instance of the paper is included
--   - encoding: service times with nth moments τ(n)_i > 0, finiteness not stated → finite second moments ∫ x² dS_i < ∞ for every type; reason: without them the means in (3)–(4) are ∞ − ∞ and the statement is undefined; this only excludes such instances
--   - encoding: types 1, …, K, pair (k, k+1) with k ∈ {1, …, K−1}; ρ̄_{k−1}, ρ̄_{k+1}, Σ_{ℓ=1}^{k−1}, Σ_{ℓ=1}^{k+1} → Fin K (0-based), pair of types k, k+1 with k+1 < K; rhoBar k, rhoBar (k+2), sumP2 k, sumP2 (k+2); reason: index shift only: the paper's k is k+1 here, and rhoBar m is the paper's ρ̄_m
--   - reading: 'without loss of generality, type i customers have priority order i under policy π' (p. 4) → π_k gives type i order i; π_{k+1} swaps the orders of k and k+1; π̄_k gives k and k+1 one common order and keeps the order of all other types; reason: the setting of every displayed formula of the paper (ρ̄_{k−1}, ρ̄_{k+1}, (A.8)–(A.10))
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, Proposition 2, p.5 (PDF 6)

import Mathlib
import Definitions.Def_NonlinearPriority_IsLongRunAvgCost
import Definitions.Def_NonlinearPriority_delta

open MeasureTheory

namespace NonlinearPriority

/-- **Proposition 2: a cμ-rule for general costs** (p. 5, PDF 6). Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

"Suppose that Assumption 1 holds under policies πk, πk+1, and π̄k for fixed k ∈ {1, 2, …, K − 1}
and let δ^{γ1,γ2}_i ≡ (E[Ci(W^{γ1}_i)] − E[Ci(W^{γ2}_i)]) / (E[W^{γ1}_i] − E[W^{γ2}_i]) (3) for
i ∈ {k, k + 1}, γ1, γ2 ∈ {πk, πk+1, π̄k}, and γ1 ≠ γ2. Then, we have
a. Cπk ≤ Cπ̄k if and only if δ^{πk,π̄k}_k μk ≥ δ^{πk,π̄k}_{k+1} μk+1.
b. Cπk+1 ≤ Cπ̄k if and only if δ^{πk+1,π̄k}_{k+1} μk+1 ≥ δ^{πk+1,π̄k}_k μk.
c. Cπk ≤ Cπk+1 if and only if δ^{πk,πk+1}_k μk ≥ δ^{πk,πk+1}_{k+1} μk+1."

`a`, `b` are the types `k`, `k + 1` (0-based); `cK`, `cK1`, `cBar` are the long-run average costs
(1) of `π_k`, `π_{k+1}`, `π̄_k`.

**Formalization Note.** Finite second moments of service make every mean in (3) finite; the
denominators of (3) are then nonzero (Lemma A.1(c)). Cost functions are only assumed measurable. -/
theorem proposition_2 {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
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
    (cK ≤ cBar ↔ delta C w (piK k) (piBar k) a * P.mu a ≥ delta C w (piK k) (piBar k) b * P.mu b) ∧
    (cK1 ≤ cBar ↔
      delta C w (piK1 k) (piBar k) b * P.mu b ≥ delta C w (piK1 k) (piBar k) a * P.mu a) ∧
    (cK ≤ cK1 ↔
      delta C w (piK k) (piK1 k) a * P.mu a ≥ delta C w (piK k) (piK1 k) b * P.mu b) := by sorry

end NonlinearPriority

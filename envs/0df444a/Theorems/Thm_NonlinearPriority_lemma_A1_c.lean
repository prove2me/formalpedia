-- Prove2me | Theorems.Thm_NonlinearPriority_lemma_A1_c
-- name    : NonlinearPriority.lemma_A1_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:27.654979+00:00
-- url     : https://prove2.me/theorems/5c13602d-a273-4172-88ff-0c71b65b0f21
-- title:
--   Lemma A.1(c), p.15 — mean steady-state waits under $\bar\pi_k$ and $\pi_i$
-- statement:
--   Assume finite second moments of service, and let $i\in\{k,k+1\}$ with $j$ the other type of the pair. Then
--   $$\mathbb E[W^{\bar\pi_k}]=\frac{\lambda\tau^{(2)}}{2\bar\rho_{k+1}\bar\rho_{k-1}},\qquad \mathbb E[W^{\pi_i}_i]=\frac{\lambda\tau^{(2)}}{2(\bar\rho_{k-1}-\rho_i)\bar\rho_{k-1}},\qquad \mathbb E[W^{\pi_i}_j]=\frac{\lambda\tau^{(2)}}{2\bar\rho_{k+1}(\bar\rho_{k-1}-\rho_i)} .$$
--
--   These are Cobham's formulas for the nonpreemptive priority queue. They show that the means in (3) and (4) differ, so $\delta$ and $M$ are well defined.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - encoding: types 1, …, K, pair (k, k+1) with k ∈ {1, …, K−1}; ρ̄_{k−1}, ρ̄_{k+1}, Σ_{ℓ=1}^{k−1}, Σ_{ℓ=1}^{k+1} → Fin K (0-based), pair of types k, k+1 with k+1 < K; rhoBar k, rhoBar (k+2), sumP2 k, sumP2 (k+2); reason: index shift only: the paper's k is k+1 here, and rhoBar m is the paper's ρ̄_m
--   - encoding: service times with nth moments τ(n)_i > 0, finiteness not stated → finite second moments ∫ x² dS_i < ∞ for every type; reason: without them the means in (3)–(4) are ∞ − ∞ and the statement is undefined; this only excludes such instances
--   - encoding: E[W^{π̄k}] and E[(W^{π̄k})²] without a type subscript ('W^{π̄k}_k and W^{π̄k}_{k+1} are identical', p. 5) → the type-i law under π̄_k for each type i of the pair; reason: the literal δ^{γ,π̄k}_i of (3); the paper identifies the two laws
--   - reading: 'without loss of generality, type i customers have priority order i under policy π' (p. 4) → π_k gives type i order i; π_{k+1} swaps the orders of k and k+1; π̄_k gives k and k+1 one common order and keeps the order of all other types; reason: the setting of every displayed formula of the paper (ρ̄_{k−1}, ρ̄_{k+1}, (A.8)–(A.10))
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, Lemma A.1(c), p.15 (PDF 16)

import Mathlib
import Definitions.Def_NonlinearPriority_IsSteadyStateLaw
import Definitions.Def_NonlinearPriority_piBar

open MeasureTheory

namespace NonlinearPriority

/-- **Lemma A.1(c): mean waiting times** (p. 15, PDF 16). Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

"E[W^{π̄k}] = λτ(2) / (2ρ̄k+1 ρ̄k−1), E[W^{πi}_i] = λτ(2) / (2(ρ̄k−1 − ρi)ρ̄k−1),
E[W^{πi}_{2k+1−i}] = λτ(2) / (2ρ̄k+1(ρ̄k−1 − ρi)), for i ∈ {k, k + 1}."

For `i` in the pair and `j` the other type (`2k + 1 − i`), with finite second moments of service.

**Formalization Note.** 0-based types: the paper's `k` is `k + 1` here, so its `ρ̄_{k−1}` is
`rhoBar k` and its `ρ̄_{k+1}` is `rhoBar (k + 2)`. `E[W^{π̄k}]` is stated for the type-`i` law
under `π̄_k`, for both types of the pair. -/
theorem lemma_A1_c {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr)
    (hS2 : ∀ l, Integrable (fun x => x ^ 2) (P.S l))
    (k : ℕ) (i j : Fin K) (hij : ((i : ℕ) = k ∧ (j : ℕ) = k + 1) ∨ ((i : ℕ) = k + 1 ∧ (j : ℕ) = k))
    (wBar wii wij : ProbabilityMeasure ℝ) (hBar : IsSteadyStateLaw X (piBar k) i wBar)
    (hii : IsSteadyStateLaw X (prioPolicy k i) i wii)
    (hij' : IsSteadyStateLaw X (prioPolicy k i) j wij) :
    ∫ x, x ∂(wBar : Measure ℝ) = P.lam * P.tauAll 2 / (2 * P.rhoBar (k + 2) * P.rhoBar k) ∧
    ∫ x, x ∂(wii : Measure ℝ) =
      P.lam * P.tauAll 2 / (2 * (P.rhoBar k - P.rho i) * P.rhoBar k) ∧
    ∫ x, x ∂(wij : Measure ℝ) =
      P.lam * P.tauAll 2 / (2 * P.rhoBar (k + 2) * (P.rhoBar k - P.rho i)) := by sorry

end NonlinearPriority

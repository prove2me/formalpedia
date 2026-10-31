-- Prove2me | Theorems.Thm_NonlinearPriority_lemma_A1_a
-- name    : NonlinearPriority.lemma_A1_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:24.441274+00:00
-- url     : https://prove2.me/theorems/1ef5f758-1a6f-40c2-b9c7-3a048ae553d2
-- title:
--   Lemma A.1(a), p.15 — the other types' steady-state waits are the same under $\pi_k,\pi_{k+1},\bar\pi_k$
-- statement:
--   Fix adjacent types $k,k+1$ and a type $j\notin\{k,k+1\}$. The steady-state waiting times of type $j$ under $\pi_k$, $\pi_{k+1}$ and $\bar\pi_k$ have the same distribution:
--   $$W^{\pi_k}_j\overset{st}{=}W^{\pi_{k+1}}_j\overset{st}{=}W^{\bar\pi_k}_j .$$
--
--   Changing the priorities inside the pair $k,k+1$ therefore affects only those two types, which reduces every comparison of the three policies to types $k$ and $k+1$.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - encoding: types 1, …, K, pair (k, k+1) with k ∈ {1, …, K−1}; ρ̄_{k−1}, ρ̄_{k+1}, Σ_{ℓ=1}^{k−1}, Σ_{ℓ=1}^{k+1} → Fin K (0-based), pair of types k, k+1 with k+1 < K; rhoBar k, rhoBar (k+2), sumP2 k, sumP2 (k+2); reason: index shift only: the paper's k is k+1 here, and rhoBar m is the paper's ρ̄_m
--   - reading: 'without loss of generality, type i customers have priority order i under policy π' (p. 4) → π_k gives type i order i; π_{k+1} swaps the orders of k and k+1; π̄_k gives k and k+1 one common order and keeps the order of all other types; reason: the setting of every displayed formula of the paper (ρ̄_{k−1}, ρ̄_{k+1}, (A.8)–(A.10))
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, Lemma A.1(a), p.15 (PDF 16)

import Mathlib
import Definitions.Def_NonlinearPriority_IsSteadyStateLaw
import Definitions.Def_NonlinearPriority_piBar

open MeasureTheory

namespace NonlinearPriority

/-- **Lemma A.1(a): the other types are unaffected** (p. 15, PDF 16). Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

"W^{πk}_j =st W^{πk+1}_j =st W^{π̄k}_j for j ∈ {1,2,...,K} \ {k,k + 1}, where =st means
equivalence in distribution."

If `w₁, w₂, w₃` are the steady-state waiting-time laws of a type `j` outside the pair under
`π_k`, `π_{k+1}` and `π̄_k`, they are equal.

**Formalization Note.** Types are 0-based: the pair is `k, k+1` with `k + 1 < K`. -/
theorem lemma_A1_a {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr)
    (k : ℕ) (hk : k + 1 < K) (j : Fin K) (hjk : (j : ℕ) ≠ k) (hjk1 : (j : ℕ) ≠ k + 1)
    (w₁ w₂ w₃ : ProbabilityMeasure ℝ) (h₁ : IsSteadyStateLaw X (piK k) j w₁)
    (h₂ : IsSteadyStateLaw X (piK1 k) j w₂) (h₃ : IsSteadyStateLaw X (piBar k) j w₃) :
    w₁ = w₂ ∧ w₂ = w₃ := by sorry

end NonlinearPriority

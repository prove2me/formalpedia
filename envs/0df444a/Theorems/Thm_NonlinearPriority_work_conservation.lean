-- Prove2me | Theorems.Thm_NonlinearPriority_work_conservation
-- name    : NonlinearPriority.work_conservation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:26.19498+00:00
-- url     : https://prove2.me/theorems/47b539e0-1ec1-46ba-b583-56e9dc6627fe
-- title:
--   Proof of Proposition 2, p.18 — the work conservation law $\sum_j p_j\mathbb E[W_j]/\mu_j$
-- statement:
--   Assume finite second moments of service. For any two fixed-priority policies $\gamma_1,\gamma_2$ whose steady-state waiting-time laws exist for every type,
--   $$\sum_{j=1}^K\frac{p_j\,\mathbb E[W^{\gamma_1}_j]}{\mu_j}=\sum_{j=1}^K\frac{p_j\,\mathbb E[W^{\gamma_2}_j]}{\mu_j}.$$
--
--   The paper uses this (Kleinrock's conservation law) for $\gamma_1=\pi_k$, $\gamma_2=\bar\pi_k$ and the analogous pairs in parts (b) and (c) of Proposition 2: the mean work in queue does not depend on the priority orders.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - encoding: service times with nth moments τ(n)_i > 0, finiteness not stated → finite second moments ∫ x² dS_i < ∞ for every type; reason: without them the means in (3)–(4) are ∞ − ∞ and the statement is undefined; this only excludes such instances
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
--   - generalization: the display for π_k and π̄_k (and, by 'very similar' proofs, the other pairs of {π_k, π_{k+1}, π̄_k}) → any two order maps ord₁, ord₂; reason: Kleinrock's law holds for every policy of Π^F; taking ord₁ = π_k, ord₂ = π̄_k gives the display
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, proof of Proposition 2, work-conservation display, p.18 (PDF 19)

import Mathlib
import Definitions.Def_NonlinearPriority_IsSteadyStateLaw

open MeasureTheory

namespace NonlinearPriority

/-- **The work conservation law** (proof of Proposition 2, p. 18, PDF 19). Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

"According to the work conservation law (see, e.g., Kleinrock 1965), we have
Σ_{j=1}^K pj E[W^{πk}_j]/μj = Σ_{j=1}^K pj E[W^{π̄k}_j]/μj,"

For any two fixed-priority policies with steady-state laws for every type and finite second
moments of service, `Σⱼ pⱼ E[Wⱼ]/μⱼ` is the same. -/
theorem work_conservation {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr)
    (hS2 : ∀ l, Integrable (fun x => x ^ 2) (P.S l))
    (ord₁ ord₂ : Fin K → ℕ) (w₁ w₂ : Fin K → ProbabilityMeasure ℝ)
    (h₁ : ∀ i, IsSteadyStateLaw X ord₁ i (w₁ i)) (h₂ : ∀ i, IsSteadyStateLaw X ord₂ i (w₂ i)) :
    ∑ j, P.p j * (∫ x, x ∂(w₁ j : Measure ℝ)) / P.mu j =
      ∑ j, P.p j * (∫ x, x ∂(w₂ j : Measure ℝ)) / P.mu j := by sorry

end NonlinearPriority

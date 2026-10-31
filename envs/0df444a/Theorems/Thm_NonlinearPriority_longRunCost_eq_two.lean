-- Prove2me | Theorems.Thm_NonlinearPriority_longRunCost_eq_two
-- name    : NonlinearPriority.longRunCost_eq_two
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:34.959019+00:00
-- url     : https://prove2.me/theorems/7afdbf01-0999-44c3-8fb9-09e249fba93a
-- title:
--   §3, p.4 — the limit (1) exists and equals $\lambda\sum_i p_i\mathbb E[C_i(W^\pi_i)]$, (2)
-- statement:
--   Let $\pi$ be a fixed-priority policy (any priority-order map, served FCFS within an order) in the stable multiclass queue. Suppose that for every type $i$ the steady-state waiting-time law $W^\pi_i$ exists and that Assumption 1 holds: $\mathbb E[|C_i(W^\pi_i)|]<\infty$ for all $i$, the costs $C_i$ being measurable. Then the long-run average cost (1) exists, from every initial state almost surely, and
--   $$C^\pi=\lambda\sum_{i=1}^K p_i\,\mathbb E\bigl[C_i(W^\pi_i)\bigr].\tag{2}$$
--
--   This turns the sample-path cost into a steady-state expectation, and every comparison of policies in the paper starts from it.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - reading: C^π ≡ lim_{t→∞} Σ_i Σ_{k ≤ n_i(t)} C_i(V^{π,x0}_{i,k})/t (1), a random limit with x0 only in the notation → IsLongRunAvgCost: the constant c such that, for every initial state x0, the average converges to c almost surely; reason: the strongest reading; §A.2.1 proves it from every initial state
--   - generalization: each C_i differentiable and nondecreasing (p. 3) → each C_i an arbitrary measurable function, subject to Assumption 1; reason: only the integrability of C_i(W) is used; differentiable functions are measurable, so every instance of the paper is included
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
--   - reading: 'for any policy π ∈ Π' (nonidling, nonpreemptive, fixed priority orders, within-order discipline unspecified) → every policy of Π^F, given by an order map with FCFS within an order; reason: the paper never specifies the within-order discipline of Π \ Π^F (nor the information it may use), so Π^F is the part of Π the model defines; the paper uses (2) only for policies of Π^F
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, §3, p.4 (PDF 5), eq. (2); proof §A.2.1, (A.3)–(A.4), pp.16–18 (PDF 17–19)

import Mathlib
import Definitions.Def_NonlinearPriority_IsLongRunAvgCost

open MeasureTheory

namespace NonlinearPriority

/-- **The long-run average cost (1) exists and equals (2)** (§3, p. 4, PDF 5; proof §A.2.1,
pp. 16–18, PDF 17–19). Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

"We show in the appendix that the limit in (1) exists and satisfies
Cπ = λ Σ_{i=1}^K pi E[Ci(W^π_i)] (2) if Assumption 1 holds."

For every fixed-priority policy `ord` (any order map, i.e. any policy of `Π^F`), if `w i` is the
steady-state waiting-time law of type `i` and `E|Cᵢ(W_i)| < ∞` for every `i` (Assumption 1), then
from every initial state the average (1) converges almost surely to `λ Σᵢ pᵢ ∫ Cᵢ dwᵢ`.

**Formalization Note.** Stability `ρ < 1` is a field of `Params`. The cost functions are only
assumed measurable (the paper: differentiable and nondecreasing). -/
theorem longRunCost_eq_two {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr)
    (C : Fin K → ℝ → ℝ) (hC : ∀ i, Measurable (C i)) (ord : Fin K → ℕ)
    (w : Fin K → ProbabilityMeasure ℝ) (hw : ∀ i, IsSteadyStateLaw X ord i (w i))
    (hA1 : ∀ i, Integrable (C i) (w i : Measure ℝ)) :
    IsLongRunAvgCost X C ord (P.lam * ∑ i, P.p i * ∫ x, C i x ∂(w i : Measure ℝ)) := by sorry

end NonlinearPriority

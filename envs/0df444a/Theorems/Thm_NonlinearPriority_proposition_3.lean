-- Prove2me | Theorems.Thm_NonlinearPriority_proposition_3
-- name    : NonlinearPriority.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:25:33.273989+00:00
-- url     : https://prove2.me/theorems/768e3ff2-c16d-4926-bac1-1ff421b4b3dc
-- title:
--   Proposition 3, p.6 — under quadratic costs, prioritize $k$, prioritize $k+1$, or pool them under FCFS
-- statement:
--   Fix adjacent types $k,k+1$. Suppose that for $i\in\{k,k+1\}$ the waiting costs are quadratic,
--   $$C_i(t)=c^{(2)}_it^2+c^{(1)}_it\quad(t\ge0),\qquad c^{(1)}_i,c^{(2)}_i\ge0,$$
--   that service times have finite second moments, that the steady-state waiting-time laws exist for every type under $\pi_k$, $\pi_{k+1}$, $\bar\pi_k$, and that Assumption 1 holds under these policies: $\mathbb E[|C_i(W^\gamma_i)|]<\infty$ for every type $i$. Write $\delta^\gamma_i=\delta^{\gamma,\bar\pi_k}_i$ (3). Then:
--
--   1. the long-run average costs $C^{\pi_k}$, $C^{\pi_{k+1}}$, $C^{\bar\pi_k}$ of (1) exist;
--   2. for $i,j\in\{k,k+1\}$, $j\ne i$: $\delta^{\pi_i}_i\le\delta^{\pi_j}_i$, with strict inequality if and only if $c^{(2)}_i>0$;
--   3. $\delta^\gamma_i=c^{(2)}_iM^\gamma_i+c^{(1)}_i$ for $i\in\{k,k+1\}$ and $\gamma\in\{\pi_k,\pi_{k+1}\}$, with $M^\gamma_i$ from (4);
--   4. the best of the three policies is characterized as follows:
--      - (a) if $\delta^{\pi_k}_k\mu_k>\delta^{\pi_k}_{k+1}\mu_{k+1}$, then $C^{\pi_k}<C^{\bar\pi_k}<C^{\pi_{k+1}}$: $\pi_k$ is the best and $\pi_{k+1}$ the worst;
--      - (b) if $\delta^{\pi_{k+1}}_{k+1}\mu_{k+1}>\delta^{\pi_{k+1}}_k\mu_k$, then $C^{\pi_{k+1}}<C^{\bar\pi_k}<C^{\pi_k}$;
--      - (c) otherwise, i.e. if $\delta^{\pi_k}_k\mu_k\le\delta^{\pi_k}_{k+1}\mu_{k+1}$ and $\delta^{\pi_{k+1}}_{k+1}\mu_{k+1}\le\delta^{\pi_{k+1}}_k\mu_k$, then $C^{\bar\pi_k}\le C^{\pi_k}$ and $C^{\bar\pi_k}\le C^{\pi_{k+1}}$: pooling is the best.
--
--   This generalizes the $c\mu$-rule to quadratic costs. Unlike the linear case, giving priority to either type can be worse than not prioritizing at all, and the pooled FCFS policy $\bar\pi_k$ is never the worst of the three.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - reading: C^π ≡ lim_{t→∞} Σ_i Σ_{k ≤ n_i(t)} C_i(V^{π,x0}_{i,k})/t (1), a random limit with x0 only in the notation → IsLongRunAvgCost: the constant c such that, for every initial state x0, the average converges to c almost surely; reason: the strongest reading; §A.2.1 proves it from every initial state
--   - reading: Assumption 1: 'For π ∈ Π and all i, E[|C_i(W^π_i)|] < ∞' → Integrable (C i) under π_k, π_{k+1} and π̄_k only, for every type i; reason: Proposition 2 states it this way; only these three policies enter, and the weaker hypothesis makes the theorem stronger
--   - reading: 'π_k is the best (and π_{k+1} is the worst)', 'π̄_k is the best' → strict in (a) and (b): C^{π_k} < C^{π̄_k} < C^{π_{k+1}} (and symmetrically); weak in (c): C^{π̄_k} ≤ C^{π_k} and C^{π̄_k} ≤ C^{π_{k+1}}; reason: strict is the stronger reading and is true under the strict hypotheses of (a)/(b); (c) cannot be strict (linear costs with c_kμ_k = c_{k+1}μ_{k+1} make all three costs equal)
--   - reading: 'without loss of generality, type i customers have priority order i under policy π' (p. 4) → π_k gives type i order i; π_{k+1} swaps the orders of k and k+1; π̄_k gives k and k+1 one common order and keeps the order of all other types; reason: the setting of every displayed formula of the paper (ρ̄_{k−1}, ρ̄_{k+1}, (A.8)–(A.10))
--   - encoding: service times with nth moments τ(n)_i > 0, finiteness not stated → finite second moments ∫ x² dS_i < ∞ for every type; reason: without them the means in (3)–(4) are ∞ − ∞ and the statement is undefined; this only excludes such instances
--   - encoding: types 1, …, K, pair (k, k+1) with k ∈ {1, …, K−1}; ρ̄_{k−1}, ρ̄_{k+1}, Σ_{ℓ=1}^{k−1}, Σ_{ℓ=1}^{k+1} → Fin K (0-based), pair of types k, k+1 with k+1 < K; rhoBar k, rhoBar (k+2), sumP2 k, sumP2 (k+2); reason: index shift only: the paper's k is k+1 here, and rhoBar m is the paper's ρ̄_m
--   - encoding: E[W^{π̄k}] and E[(W^{π̄k})²] without a type subscript ('W^{π̄k}_k and W^{π̄k}_{k+1} are identical', p. 5) → the type-i law under π̄_k for each type i of the pair; reason: the literal δ^{γ,π̄k}_i of (3); the paper identifies the two laws
--   - generalization: every C_i differentiable and nondecreasing; C_i(t) = c(2)_i t² + c(1)_i t for t ≥ 0, i ∈ {k, k+1} → C_j arbitrary measurable for j ∉ {k, k+1}; for i ∈ {k, k+1}, C_i measurable on ℝ and quadratic on t ≥ 0; reason: only Assumption 1 is used for the other types, and waiting times are nonnegative; the paper's costs are measurable
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, Proposition 3, p.6 (PDF 7); Assumption 1, p.4 (PDF 5)

import Mathlib
import Definitions.Def_NonlinearPriority_IsLongRunAvgCost
import Definitions.Def_NonlinearPriority_delta
import Definitions.Def_NonlinearPriority_Mval

open MeasureTheory

namespace NonlinearPriority

/-- **Proposition 3: the best of `π_k`, `π_{k+1}`, `π̄_k` under quadratic costs** (p. 6, PDF 7).
Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

"Suppose that Assumption 1 holds and, for fixed k ∈ {1, 2, …, K − 1} and i ∈ {k, k + 1}, cost
functions satisfy Ci(t) = c(2)_i t² + c(1)_i t, where t ≥ 0 and c(1)_i, c(2)_i ≥ 0. Then,
δ^{πi}_i ≤ δ^{πj}_i for i, j ∈ {k, k + 1} and j ≠ i, where δ^γ_i = c(2)_i M^γ_i + c(1)_i for
γ ∈ {πk, πk+1}, and the inequality holds strictly if and only if c(2)_i > 0. Furthermore, the best
policy among πk, πk+1, and π̄k is characterized as follows:
a. If δ^{πk}_k μk > δ^{πk}_{k+1} μk+1, then πk is the best (and πk+1 is the worst).
b. If δ^{πk+1}_{k+1} μk+1 > δ^{πk+1}_k μk, then πk+1 is the best (and πk is the worst).
c. Otherwise, that is, if δ^{πk}_k μk ≤ δ^{πk}_{k+1} μk+1 and δ^{πk+1}_{k+1} μk+1 ≤ δ^{πk+1}_k μk,
π̄k is the best."

Assumption 1 (p. 4): "E[|Ci(W^π_i)|] < ∞", here under `π_k`, `π_{k+1}`, `π̄_k` for every type.

Conclusions: (1) the long-run average costs (1) of the three policies exist; (2) the first claim;
(3) the formula for `δ^γ_i`; (4) parts a–c, with "best" and "worst" strict in a and b and "best"
weak in c.

**Formalization Note.** `a`, `b` are the types `k`, `k + 1` (0-based; the paper's `k` is `k + 1`).
`π_i` is `prioPolicy k i`. `δ^γ_i` is `deltaBar` (= `δ^{γ,π̄k}_i` of (3)) and `M^γ_i` is (4), both
with the type-`i` law under `π̄_k`. Finite second moments of service keep the means in (3)–(4)
finite. Cost functions are measurable; for the two types of the pair they are quadratic on
`t ≥ 0`. -/
theorem proposition_3 {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr)
    (hS2 : ∀ l, Integrable (fun x => x ^ 2) (P.S l))
    (C : Fin K → ℝ → ℝ) (hC : ∀ i, Measurable (C i))
    (k : ℕ) (a b : Fin K) (ha : (a : ℕ) = k) (hb : (b : ℕ) = k + 1)
    (c1 c2 : Fin K → ℝ) (hc1 : 0 ≤ c1 a ∧ 0 ≤ c1 b) (hc2 : 0 ≤ c2 a ∧ 0 ≤ c2 b)
    (hquad : ∀ i ∈ ({a, b} : Set (Fin K)), ∀ t : ℝ, 0 ≤ t → C i t = c2 i * t ^ 2 + c1 i * t)
    (w : (Fin K → ℕ) → Fin K → ProbabilityMeasure ℝ)
    (hw : ∀ γ ∈ ({piK k, piK1 k, piBar k} : Set (Fin K → ℕ)), ∀ i, IsSteadyStateLaw X γ i (w γ i))
    (hA1 : ∀ γ ∈ ({piK k, piK1 k, piBar k} : Set (Fin K → ℕ)), ∀ i,
      Integrable (C i) (w γ i : Measure ℝ)) :
    (∀ γ ∈ ({piK k, piK1 k, piBar k} : Set (Fin K → ℕ)), ∃ c, IsLongRunAvgCost X C γ c) ∧
    (∀ i j : Fin K, (i = a ∧ j = b) ∨ (i = b ∧ j = a) →
      deltaBar C w k (prioPolicy k i) i ≤ deltaBar C w k (prioPolicy k j) i ∧
      (deltaBar C w k (prioPolicy k i) i < deltaBar C w k (prioPolicy k j) i ↔ 0 < c2 i)) ∧
    (∀ i ∈ ({a, b} : Set (Fin K)), ∀ γ ∈ ({piK k, piK1 k} : Set (Fin K → ℕ)),
      deltaBar C w k γ i = c2 i * Mval w k γ i + c1 i) ∧
    (∀ cK cK1 cBar : ℝ, IsLongRunAvgCost X C (piK k) cK → IsLongRunAvgCost X C (piK1 k) cK1 →
      IsLongRunAvgCost X C (piBar k) cBar →
      (deltaBar C w k (piK k) a * P.mu a > deltaBar C w k (piK k) b * P.mu b →
          cK < cBar ∧ cBar < cK1) ∧
      (deltaBar C w k (piK1 k) b * P.mu b > deltaBar C w k (piK1 k) a * P.mu a →
          cK1 < cBar ∧ cBar < cK) ∧
      (deltaBar C w k (piK k) a * P.mu a ≤ deltaBar C w k (piK k) b * P.mu b ∧
          deltaBar C w k (piK1 k) b * P.mu b ≤ deltaBar C w k (piK1 k) a * P.mu a →
          cBar ≤ cK ∧ cBar ≤ cK1)) := by sorry

end NonlinearPriority

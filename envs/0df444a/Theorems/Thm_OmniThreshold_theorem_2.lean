-- Prove2me | Theorems.Thm_OmniThreshold_theorem_2
-- name    : OmniThreshold.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:44.562597+00:00
-- url     : https://prove2.me/theorems/9c62c938-7075-47db-8c48-67589689ddd7
-- title:
--   Theorem 2 — the expected total cost $G(S)$ is unimodal in the Global Threshold $S$ (corrected: independent demands, i.i.d. order locations)
-- statement:
--   **Setting.** A retailer has $n$ stores. Store $i$ holds inventory $\mathcal I_i\in\mathbb N$. Costs are a missed-sale penalty $p\ge0$, unit shipping costs $s_{ji}\ge0$ from store $j$ to store $i$, and cancellation costs $c_i$ with $s_{ji}<c_i$ for all $i,j$. On a probability space $(\Omega,\mathbb P)$, online orders arrive at the locations $X_0,X_1,\dots$. In total $N$ of them arrive, so the online demand at $i$ is $\mathcal D_i^O=\#\{k<N:X_k=i\}$, and $\mathcal D^P$ is the vector of in-store demands. All are measurable.
--
--   A Global Threshold $S$ accepts the first $S$ online orders. Let $G(S)$ be the expected optimal value of the second-stage problem LP (1) under this policy.
--
--   **Assumptions.**
--
--   1. The order locations are independent and identically distributed.
--   2. The sequence of locations is independent of $(N,\mathcal D^P)$.
--   3. $N$ is independent of $\mathcal D^P$.
--
--   **Conclusion.** $G$ is unimodal. Precisely, $G$ has a minimizer, and every minimizer $S^*$ satisfies
--   $$
--   G(S+1)\le G(S)\quad\text{for all } S<S^*,\qquad G(S)\le G(S+1)\quad\text{for all } S\ge S^*.
--   $$
--
--   This is the paper's structural result for Global Thresholds. It justifies searching for the optimal threshold by local, gradient-type methods.
--
--   **Formalization Note** In-store demand may have any joint law across stores, and $N$ any law on $\mathbb N$.
--
--   Differences from the source:
--   - correction: no assumption on the joint law of online and in-store demand → assumptions 1–3; reason: as printed the theorem is false. With one store, $\mathcal I=2$, $p=1$, $c=2$, $s=0$, and $(\mathcal D^O,\mathcal D^P)\in\{(1,2),(3,0)\}$ with probability $\tfrac12$ each (dependent demands), $G(0),G(1),G(2),\dots=1,\tfrac32,1,2,2,\dots$, which has two strict local minima. Assumption 1 is needed as well, even for constant $N$ and $\mathcal D^P$: with two stores, $\mathcal I=(0,2)$, $\mathcal D^P=0$, $N=2$, $p=1$, $c_i=6$, $s_{10}=5$, the other $s_{ji}=0$, and the deterministic locations $X_0=0$, $X_k=1$ for $k\ge1$, $G(0),G(1),G(2),G(3),\dots=2,6,5,5,\dots$, so the only minimizer is $S^*=0$ and $G(2)<G(1)$. The paper's own proofs use these assumptions: App. A (p.27) integrates against the product density, App. D (p.33) states "Since $D_1^O$ and $D_1^P$ are independent", and the proof of Theorem 2 draws order locations "from a common probability distribution" (p.10)
--   - reading: "unimodal" → a minimizer exists, and every minimizer $S^*$ has $G(S+1)\le G(S)$ for $S<S^*$ and $G(S)\le G(S+1)$ for $S\ge S^*$; reason: this is the meaning fixed by the proof (p.9, "Let $S^*$ be an optimal solution … We want to show that $G(S+1)-G(S)\le0$ $\forall S<S^*$ and $G(S+1)-G(S)\ge0$ $\forall S>S^*$"; p.10, "$\forall S\ge S^*$"), applied to every optimal $S^*$ as the proof does, with the existence of an optimum that the proof presupposes
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$; reason: LP (1) has per-location $c_i$; the paper's assumption is the case $c_i=c$
--   - reading: penalty and shipping costs (no sign stated) → $p\ge0$, $s_{ji}\ge0$; reason: they are costs in the model of §1.1
--   - encoding: demands $\mathcal D^O$ per location and "the first $S$ online orders" → an arrival stream $X$ with total $N$, accepted orders $\#\{k<\min(S,N):X_k=i\}$, ℕ-valued inventories and demands, real-valued LP variables, all random objects measurable; reason: the model's quantities, with the arrival order made explicit; any demand vector arises this way
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, Theorem 2, p.9; proof pp.9–10; model §1.1, pp.2–4

import Mathlib
import Definitions.Def_OmniThreshold_expectedCost

namespace OmniThreshold

open MeasureTheory ProbabilityTheory

/-- **Theorem 2** (Jia, Karp, Ravi & Tayur, *Effective Online Order Acceptance Policies for
Omni-Channel Fulfillment*, SSRN 3932692, Theorem 2, p.9; proof pp.9–10), corrected: "`G(S)`, the
expected value of the objective function of the Omni-Channel Fulfillment Model as a function of
Global Threshold `S`, is unimodal."

Model (§1.1, pp.2–4): `n` stores with inventories `I_i ∈ ℕ`, missed-sale penalty `p ≥ 0`, shipping
costs `s_ji ≥ 0` from `j` to `i` and cancellation costs `c_i > s_ji`. Online orders arrive at the
locations `X_0, X_1, …`; `N` of them arrive, and `D^P` is the vector of in-store demands.
`G(S) = expectedCost … P S` is the expected optimal value of LP (1) when the first `S` orders are
accepted. Assume (correction) that the order locations are i.i.d., that the sequence of locations is
independent of `(N, D^P)`, and that `N` is independent of `D^P`. Then `G` has a minimizer, and every
minimizer `S*` satisfies `G(S+1) ≤ G(S)` for `S < S*` and `G(S) ≤ G(S+1)` for `S ≥ S*`.

**Formalization Note** "Unimodal" has the meaning fixed by the proof (p.9: "Let `S*` be an optimal
solution …, a solution that minimizes `G`. We want to show that `G(S+1) − G(S) ≤ 0 ∀ S < S*` and
`G(S+1) − G(S) ≥ 0 ∀ S > S*`"; p.10: "`∀ S ≥ S*`"), for every minimizer, together with the
existence of one. As printed (no assumption on the joint law of online and in-store demand) the
theorem is false: with one store, `I = 2`, `p = 1`, `c = 2`, `s = 0` and
`(D^O, D^P) ∈ {(1, 2), (3, 0)}` with probability `1/2` each, `G(0), G(1), G(2) = 1, 3/2, 1`. The
independence hypotheses are those the paper's own proofs use (App. A p.27, App. D p.33, and p.10).
The online demand at `i` is `#{k < N : X_k = i}` and the accepted orders `#{k < min(S, N) : X_k = i}`
(0-based arrivals). -/
theorem theorem_2 {n : ℕ} (I : Fin n → ℕ) (p : ℝ) (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ)
    (hp : 0 ≤ p) (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (DP : Ω → Fin n → ℕ)
    (hX : ∀ k, Measurable (X k)) (hN : Measurable N) (hDP : Measurable DP)
    (hiid : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hXND : IndepFun (fun ω k => X k ω) (fun ω => (N ω, DP ω)) P) (hNDP : IndepFun N DP P) :
    (∃ S₀ : ℕ, ∀ S : ℕ, expectedCost p c s I X N DP P S₀ ≤ expectedCost p c s I X N DP P S) ∧
    ∀ S₀ : ℕ, (∀ S : ℕ, expectedCost p c s I X N DP P S₀ ≤ expectedCost p c s I X N DP P S) →
      (∀ S < S₀, expectedCost p c s I X N DP P (S + 1) ≤ expectedCost p c s I X N DP P S) ∧
      (∀ S : ℕ, S₀ ≤ S →
        expectedCost p c s I X N DP P S ≤ expectedCost p c s I X N DP P (S + 1)) := by sorry

end OmniThreshold

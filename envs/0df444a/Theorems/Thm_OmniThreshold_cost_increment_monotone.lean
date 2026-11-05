-- Prove2me | Theorems.Thm_OmniThreshold_cost_increment_monotone
-- name    : OmniThreshold.cost_increment_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:51.607968+00:00
-- url     : https://prove2.me/theorems/63d110fb-6725-429a-9aeb-80905bdddd08
-- title:
--   Proof of Theorem 2, p.10 — $G(S+1,D(S))-G(S,D(S))$ is increasing in $S$ (corrected: independent demands, i.i.d. order locations)
-- statement:
--   Let $p\ge0$, $s_{ji}\ge0$ and $s_{ji}<c_i$. Let $(X,N,\mathcal D^P)$ be measurable random objects on a probability space $(\Omega,\mathbb P)$, and assume:
--
--   1. the order locations $X_0,X_1,\dots$ are i.i.d.;
--   2. the sequence $(X_k)$ is independent of $(N,\mathcal D^P)$;
--   3. $N$ is independent of $\mathcal D^P$.
--
--   Write $D(S)=\mathbb P[\,\cdot\mid N>S]$. Then for all $S\le S'$ with $\mathbb P(N>S')>0$,
--   $$
--   G(S+1,D(S))-G(S,D(S))\le G(S'+1,D(S'))-G(S',D(S')).
--   $$
--   The proof of Theorem 2 obtains this as the sum of the missed-sales and fulfillment increments. Together with the sign equivalence on $D(S)$, it gives the unimodality of $G$.
--
--   Differences from the source:
--   - correction: no assumption on the joint law of the demands → hypotheses 1–3; reason: otherwise the claim is false. With one store, $\mathcal I=2$, $p=1$, $c=2$, $s=0$, and $(N,\mathcal D^P)\in\{(3,0),(1,2)\}$ with probability $\tfrac12$ each, the increment is $\tfrac12$ at $S=0$ and $-1$ at $S=1$, although $\mathbb P(N>1)=\tfrac12>0$. Hypothesis 1 is needed as well, even for constant $N$ and $\mathcal D^P$: with two stores, $\mathcal I=(0,2)$, $\mathcal D^P=0$, $N=2$, $p=1$, $c_i=6$, $s_{10}=5$, the other $s_{ji}=0$, and the deterministic locations $X_0=0$, $X_k=1$ for $k\ge1$, the increment is $4$ at $S=0$ and $-1$ at $S=1$
--   - reading: $D(S)$ → the normalized conditional law $\mathbb P[\,\cdot\mid N>S]$, on thresholds with $\mathbb P(N>S')>0$; reason: with the unnormalized restriction the claim fails, because the factor $\mathbb P(N>S)$ shrinks with $S$; beyond the support of $N$ there is no demand distribution $D(S)$
--   - reading: "increasing" → nondecreasing; reason: the increments can be constant
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$; reason: LP (1) has per-location $c_i$; the paper's assumption is the case $c_i=c$
--   - reading: penalty and shipping costs (no sign stated) → $p\ge0$, $s_{ji}\ge0$; reason: they are costs in the model of §1.1
--   - encoding: demands $\mathcal D^O$ per location → an arrival stream $X$ and a total $N$, all measurable; reason: as in the definitions
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.10, "… and so G(S + 1,D(S)) − G(S,D(S)) is also increasing with S"

import Mathlib
import Definitions.Def_OmniThreshold_expectedCost

namespace OmniThreshold

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, p.10: the total conditional increment is increasing** (Jia, Karp, Ravi
& Tayur, *Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692,
proof of Theorem 2, p.10: "We have seen that both `P(S+1, D(S)) − P(S, D(S))` and
`F(S+1, D(S)) − F(S, D(S))` are increasing with `S`, and so `G(S+1, D(S)) − G(S, D(S))` is also
increasing with `S`").

Under the cost assumptions `p ≥ 0`, `s_ji ≥ 0`, `s_ji < c_i`, i.i.d. order locations independent of
(`N`, `D^P`), and `N` independent of `D^P`: for `S ≤ S'` with `P(N > S') > 0`,
`G(S+1, D(S)) − G(S, D(S)) ≤ G(S'+1, D(S')) − G(S', D(S'))`, where `D(S) = P[· | N > S]`.

**Formalization Note** As in `fulfillment_increment_monotone`: "increasing" is nondecreasing on the
thresholds where `D(S)` is a probability law, and the independence hypotheses are the correction
under which Theorem 2 holds. -/
theorem cost_increment_monotone {n : ℕ} (I : Fin n → ℕ) (p : ℝ) (c : Fin n → ℝ)
    (s : Fin n → Fin n → ℝ) (hp : 0 ≤ p) (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (DP : Ω → Fin n → ℕ)
    (hX : ∀ k, Measurable (X k)) (hN : Measurable N) (hDP : Measurable DP)
    (hiid : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hXND : IndepFun (fun ω k => X k ω) (fun ω => (N ω, DP ω)) P) (hNDP : IndepFun N DP P)
    (S S' : ℕ) (hSS' : S ≤ S') (hpos : 0 < P {ω | S' < N ω}) :
    expectedCost p c s I X N DP (P[|{ω | S < N ω}]) (S + 1) -
        expectedCost p c s I X N DP (P[|{ω | S < N ω}]) S ≤
      expectedCost p c s I X N DP (P[|{ω | S' < N ω}]) (S' + 1) -
        expectedCost p c s I X N DP (P[|{ω | S' < N ω}]) S' := by sorry

end OmniThreshold

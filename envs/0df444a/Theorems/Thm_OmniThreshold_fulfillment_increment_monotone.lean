-- Prove2me | Theorems.Thm_OmniThreshold_fulfillment_increment_monotone
-- name    : OmniThreshold.fulfillment_increment_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:18.206192+00:00
-- url     : https://prove2.me/theorems/95d22353-9841-4648-91ff-99a3c48d5aba
-- title:
--   Proof of Theorem 2, p.10 — $F(S+1,D(S))-F(S,D(S))$ is increasing in $S$ (corrected: independent demands, i.i.d. order locations)
-- statement:
--   Let $s_{ji}\ge0$ and $s_{ji}<c_i$. Let $(X,N,\mathcal D^P)$ be measurable random objects on a probability space $(\Omega,\mathbb P)$, and assume:
--
--   1. the order locations $X_0,X_1,\dots$ are independent and identically distributed;
--   2. the sequence $(X_k)$ is independent of the pair $(N,\mathcal D^P)$;
--   3. $N$ is independent of $\mathcal D^P$.
--
--   Write $D(S)=\mathbb P[\,\cdot\mid N>S]$. Then for all $S\le S'$ with $\mathbb P(N>S')>0$,
--   $$
--   F(S+1,D(S))-F(S,D(S))\le F(S'+1,D(S'))-F(S',D(S')).
--   $$
--   This is the fulfillment half of the monotonicity argument for Theorem 2.
--
--   Differences from the source:
--   - correction: no assumption on the joint law of the demands → hypotheses 1–3; reason: otherwise the claim is false. With one store, $\mathcal I=2$, $c=2$, $s=0$, and $(N,\mathcal D^P)\in\{(3,0),(1,2)\}$ with probability $\tfrac12$ each, the increment is $1$ at $S=0$ and $0$ at $S=1$, although $\mathbb P(N>1)=\tfrac12>0$. Hypothesis 1 is needed as well, even for constant $N$ and $\mathcal D^P$: with two stores, $\mathcal I=(0,2)$, $\mathcal D^P=0$, $N=2$, $p=1$, $c_i=6$, $s_{10}=5$, the other $s_{ji}=0$, and the deterministic locations $X_0=0$, $X_k=1$ for $k\ge1$, the increment is $5$ at $S=0$ and $0$ at $S=1$. The paper's own proofs use these hypotheses ("orders whose locations are selected at random from a common probability distribution", p.10; App. A p.27; App. D p.33)
--   - reading: $D(S)$ → the normalized conditional law $\mathbb P[\,\cdot\mid N>S]$, on thresholds with $\mathbb P(N>S')>0$; reason: with the unnormalized restriction the claim fails, because the factor $\mathbb P(N>S)$ shrinks with $S$; beyond the support of $N$ there is no demand distribution $D(S)$
--   - reading: "increasing" → nondecreasing; reason: the increments can be constant
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$; reason: LP (2) has per-location $c_i$; the paper's assumption is the case $c_i=c$
--   - reading: shipping costs (no sign stated) → $s_{ji}\ge0$; reason: they are costs in the model of §1.1
--   - encoding: demands $\mathcal D^O$ per location → an arrival stream $X$ and a total $N$, all measurable; reason: as in the definitions
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.10, "That F(S + 1,D(S)) − F(S,D(S)) is increasing with S follows from the previous observation …"

import Mathlib
import Definitions.Def_OmniThreshold_fulfillmentCost

namespace OmniThreshold

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, p.10: the fulfillment increment is increasing** (Jia, Karp, Ravi &
Tayur, *Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692,
proof of Theorem 2, p.10: "That `F(S+1, D(S)) − F(S, D(S))` is increasing with `S` follows from
the previous observation if we consider the case when `|N| = |M| + 1` and apply the observation over
the probability distribution of possible orders `o`").

Assume the locations `X_0, X_1, …` of successive online orders are i.i.d., the sequence is
independent of the pair (total number `N` of online orders, in-store demand vector `D^P`), and `N`
is independent of `D^P`. Then for `S ≤ S'` with `P(N > S') > 0`,
`F(S+1, D(S)) − F(S, D(S)) ≤ F(S'+1, D(S')) − F(S', D(S'))`,
where `D(S) = P[· | N > S]`.

**Formalization Note** "Increasing" is read as nondecreasing, on the thresholds `S` where `D(S)` is
a probability law (`P(N > S) > 0`; beyond the support of `N`, `cond` is the zero measure). The
independence hypotheses are the correction under which Theorem 2 holds (see `theorem_2`); the paper
uses them in this step ("orders whose locations are selected at random from a common probability
distribution"). -/
theorem fulfillment_increment_monotone {n : ℕ} (I : Fin n → ℕ) (c : Fin n → ℝ)
    (s : Fin n → Fin n → ℝ) (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (DP : Ω → Fin n → ℕ)
    (hX : ∀ k, Measurable (X k)) (hN : Measurable N) (hDP : Measurable DP)
    (hiid : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hXND : IndepFun (fun ω k => X k ω) (fun ω => (N ω, DP ω)) P) (hNDP : IndepFun N DP P)
    (S S' : ℕ) (hSS' : S ≤ S') (hpos : 0 < P {ω | S' < N ω}) :
    fulfillmentCost c s I X N DP (P[|{ω | S < N ω}]) (S + 1) -
        fulfillmentCost c s I X N DP (P[|{ω | S < N ω}]) S ≤
      fulfillmentCost c s I X N DP (P[|{ω | S' < N ω}]) (S' + 1) -
        fulfillmentCost c s I X N DP (P[|{ω | S' < N ω}]) S' := by sorry

end OmniThreshold

-- Prove2me | Theorems.Thm_OmniThreshold_increment_sign_iff_cond
-- name    : OmniThreshold.increment_sign_iff_cond
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:46.503896+00:00
-- url     : https://prove2.me/theorems/95a59b20-eede-4536-9fe4-8b138600c021
-- title:
--   Proof of Theorem 2, p.9 — the sign of $G(S+1)-G(S)$ is read on $D(S)$
-- statement:
--   Let $p\ge0$, $s_{ji}\ge0$ and $s_{ji}<c_i$. Let $(X,N,\mathcal D^P)$ be measurable random objects on a probability space $(\Omega,\mathbb P)$: the order locations, the total number of online orders, and the in-store demands. For a Global Threshold $S$, let $D(S)=\mathbb P[\,\cdot\mid N>S]$ be the demand law restricted to outcomes with $\sum_i\mathcal D_i^O>S$. Then
--   $$
--   G(S+1)>G(S)\iff G(S+1,D(S))>G(S,D(S)),
--   \qquad
--   G(S+1)<G(S)\iff G(S+1,D(S))<G(S,D(S)).
--   $$
--   The reason is that on outcomes with $N\le S$ the thresholds $S$ and $S+1$ accept the same orders. No independence is assumed.
--
--   **Formalization Note** $D(S)$ is `ProbabilityTheory.cond`. When $\mathbb P(N>S)=0$ it is the zero measure, and both sides of each equivalence are false, because then $G(S+1)=G(S)$.
--
--   Differences from the source:
--   - reading: $D(S)$, "the true demand distribution restricted to only outcomes where $\sum_i\mathcal D_i^O>S$" → the normalized conditional law $\mathbb P[\,\cdot\mid N>S]$; reason: it must be a demand distribution for $G(\cdot,D(S))$ to be defined; for the sign equivalences the normalized and unnormalized restrictions agree
--   - encoding: demands $\mathcal D^O$ per location → an arrival stream $X_0,X_1,\dots$ of order locations and a total $N$, with $\mathcal D_i^O=\#\{k<N: X_k=i\}$, all measurable; reason: "the first $S$ online orders" needs the arrival order; any demand vector arises this way
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$; reason: LP (1) has per-location $c_i$; the paper's assumption is the case $c_i=c$
--   - reading: penalty and shipping costs (no sign stated) → $p\ge0$, $s_{ji}\ge0$; reason: they are costs in the model of §1.1
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.9, "We observe that G(S+1) > G(S) if and only if G(S+1,D(S)) > G(S,D(S))"

import Mathlib
import Definitions.Def_OmniThreshold_expectedCost

namespace OmniThreshold

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, p.9: the sign of `G(S+1) − G(S)` is read on `D(S)`** (Jia, Karp, Ravi &
Tayur, *Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692,
proof of Theorem 2, p.9: "let `D(S)` be the true demand distribution restricted to only outcomes
where `∑_i D_i^O > S`. We observe that `G(S+1) > G(S)` if and only if `G(S+1, D(S)) > G(S, D(S))`
and likewise `G(S+1) < G(S)` if and only if `G(S+1, D(S)) < G(S, D(S))`").

For every Global Threshold `S`, with `D(S)` the conditional law `P[· | N > S]`,
`G(S+1) > G(S) ⟺ G(S+1, D(S)) > G(S, D(S))` and `G(S+1) < G(S) ⟺ G(S+1, D(S)) < G(S, D(S))`.

**Formalization Note** `N = ∑_i D_i^O` is the total number of online orders, `X k` the location of
the `k`-th one, `DP` the in-store demand vector; all are measurable, and no independence is
assumed. `D(S)` is `ProbabilityTheory.cond P {ω | S < N ω}`; when `P(N > S) = 0` it is the zero
measure and both sides of each equivalence are false, as `G(S+1) = G(S)` then. -/
theorem increment_sign_iff_cond {n : ℕ} (I : Fin n → ℕ) (p : ℝ) (c : Fin n → ℝ)
    (s : Fin n → Fin n → ℝ) (hp : 0 ≤ p) (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (DP : Ω → Fin n → ℕ)
    (hX : ∀ k, Measurable (X k)) (hN : Measurable N) (hDP : Measurable DP) (S : ℕ) :
    (expectedCost p c s I X N DP P S < expectedCost p c s I X N DP P (S + 1) ↔
      expectedCost p c s I X N DP (P[|{ω | S < N ω}]) S <
        expectedCost p c s I X N DP (P[|{ω | S < N ω}]) (S + 1)) ∧
    (expectedCost p c s I X N DP P (S + 1) < expectedCost p c s I X N DP P S ↔
      expectedCost p c s I X N DP (P[|{ω | S < N ω}]) (S + 1) <
        expectedCost p c s I X N DP (P[|{ω | S < N ω}]) S) := by sorry

end OmniThreshold

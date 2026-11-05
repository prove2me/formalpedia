-- Prove2me | Theorems.Thm_OmniThreshold_missed_sales_increment
-- name    : OmniThreshold.missed_sales_increment
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:59.371096+00:00
-- url     : https://prove2.me/theorems/68807c4b-2192-4a9e-81ab-ab202335ee52
-- title:
--   Proof of Theorem 2, p.10 — the missed-sales increment is $-p\cdot\Pr(\sum_i\min(\mathcal I_i,\mathcal D_i^P)+S<\sum_i\mathcal I_i)$ (corrected: $N$ independent of $\mathcal D^P$)
-- statement:
--   Let $p\ge0$. Let $(X,N,\mathcal D^P)$ be measurable random objects on a probability space $(\Omega,\mathbb P)$, and assume the total number $N$ of online orders is independent of the in-store demand vector $\mathcal D^P$. Write $D(S)=\mathbb P[\,\cdot\mid N>S]$. Then for every $S$ with $\mathbb P(N>S)>0$,
--   $$
--   P(S+1,D(S))-P(S,D(S))=-p\cdot\Pr\Bigl(\sum_{i=1}^n\min(\mathcal I_i,\mathcal D_i^P)+S<\sum_{i=1}^n\mathcal I_i\Bigr),
--   $$
--   and the right-hand side is nondecreasing in $S$.
--
--   This is the missed-sales half of the monotonicity argument for Theorem 2.
--
--   **Formalization Note** $\Pr$ is under the original $\mathbb P$.
--
--   Differences from the source:
--   - correction: no assumption on the joint law of online and in-store demand → $N$ independent of $\mathcal D^P$; reason: otherwise the identity is false. With one store, $\mathcal I=2$, $p=1$, and $(N,\mathcal D^P)\in\{(3,0),(1,2)\}$ with probability $\tfrac12$ each, at $S=1$ the left side is $-1$ and the right side is $-\tfrac12$. Reading $\Pr$ under $D(S)$ instead does not avoid the correction: on this instance $-p\Pr$ is then $-\tfrac12$ at $S=0$ and $-1$ at $S=1$, so it is not increasing
--   - reading: $D(S)$, the demand distribution restricted to outcomes with $\sum_i\mathcal D_i^O>S$ → the normalized conditional law $\mathbb P[\,\cdot\mid N>S]$, for $S$ with $\mathbb P(N>S)>0$; reason: $P(\cdot,D(S))$ is an expectation under a demand distribution, which exists only when $\mathbb P(N>S)>0$
--   - reading: "increasing" → nondecreasing; reason: the probability can be constant in $S$
--   - reading: penalty (no sign stated) → $p\ge0$; reason: it is a cost in the model of §1.1
--   - encoding: demands $\mathcal D^O$ per location → an arrival stream $X$ and a total $N$, all measurable; reason: as in the definitions; any demand vector arises this way
--   - reading: $\Pr$, with no law named → probability under the original $\mathbb P$; reason: under $N$ independent of $\mathcal D^P$ the original and the conditional law give the same value, and the event involves only $\mathcal D^P$
--   - reading: the formula for $P(S,D)$ on p.9, whose first inner term is printed $\min(I_i-\mathcal D_i^P)$ → $\min(\mathcal I_i,\mathcal D_i^P)$; reason: a one-argument minimum is a misprint; the same sum appears with the comma in the same formula and in LP (1)
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.10, "Observe that P(S + 1,D(S)) − P(S,D(S)) = −p · Pr(…)"

import Mathlib
import Definitions.Def_OmniThreshold_missedSalesCost

namespace OmniThreshold

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, p.10: the missed-sales increment** (Jia, Karp, Ravi & Tayur, *Effective
Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, proof of Theorem 2,
p.10: "Observe that `P(S+1, D(S)) − P(S, D(S)) = −p · Pr(∑_i min(I_i, D_i^P) + S < ∑_i I_i)`.
This expression is clearly increasing in `S`, and so `P(S+1, D(S)) − P(S, D(S))` is increasing in
`S`").

If the total number `N` of online orders is independent of the in-store demand vector `D^P`, then
for every `S` with `P(N > S) > 0`,
`P(S+1, D(S)) − P(S, D(S)) = −p · Pr(∑_i min(I_i, D_i^P) + S < ∑_i I_i)`,
and the right-hand side is nondecreasing in `S`.

**Formalization Note** `D(S)` is the conditional law `P[· | N > S]`, a probability measure when
`P(N > S) > 0`; `Pr` is under the original `P` (`P.real`). The independence of `N` and `D^P` is not
stated in the paper; it is the correction under which Theorem 2 holds (see `theorem_2`), and without
it the conditional and unconditional probabilities differ. "Increasing" is read as nondecreasing. -/
theorem missed_sales_increment {n : ℕ} (I : Fin n → ℕ) (p : ℝ) (hp : 0 ≤ p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (DP : Ω → Fin n → ℕ)
    (hX : ∀ k, Measurable (X k)) (hN : Measurable N) (hDP : Measurable DP)
    (hNDP : IndepFun N DP P) :
    (∀ S : ℕ, 0 < P {ω | S < N ω} →
      missedSalesCost p I X N DP (P[|{ω | S < N ω}]) (S + 1) -
          missedSalesCost p I X N DP (P[|{ω | S < N ω}]) S =
        -p * P.real {ω | ∑ i, min (I i) (DP ω i) + S < ∑ i, I i}) ∧
    Monotone (fun S : ℕ => -p * P.real {ω | ∑ i, min (I i) (DP ω i) + S < ∑ i, I i}) := by sorry

end OmniThreshold

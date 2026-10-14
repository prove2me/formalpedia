-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_8
-- name    : GIGnBounds.Tail.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:57.480165+00:00
-- url     : https://prove2.me/theorems/aff48b0c-e837-40d1-846d-7d98b1c3d718
-- title:
--   Lemma 8 — (9) equals (10): the arrival supremum as a random-walk supremum
-- statement:
--   Let $\mathcal A_o$ be an ordinary renewal process with i.i.d. inter-event times $A_1,A_2,\dots$ of law $\mu_A$ (nonnegative, finite positive mean, rate $\mu_A=1/\mathbb E[A]$), and $A_o(t)$ its number of renewals in $[0,t]$.
--
--   **Lemma 8.** For all $\nu>0$ and $x>0$,
--
--   $$\mathbb P\Big(\sup_{t\ge0}\big(A_o(t)-\mu_At-\nu t\big)\ge x\Big)=\mathbb P\Big(\sup_{k\ge0}\Big(\frac{\mu_A}{\mu_A+\nu}k-\sum_{i=1}^k\mu_AA_i\Big)\ge x\Big(1+\frac{\nu}{\mu_A}\Big)^{-1}\Big).$$
--
--   The right side is the tail of the steady-state waiting time of a single-server queue with inter-arrival times distributed as $A\mu_A$ and constant service time $\mu_A/(\mu_A+\nu)$.
--
--   **Formalization Note.** The sequence is indexed from $0$ (the paper's $A_i$ is the $(i-1)$-st term); the empty sum ($k=0$) is $0$. Both suprema are in the extended reals.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 33, Lemma 8, displays (9)–(10)

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 8** (Li–Goldberg, arXiv:1706.04628v3, p. 33). For an ordinary renewal process `A_o` with
i.i.d. intervals `A₁, A₂, …` of law `μA` (here `X 0, X 1, …`), for all `ν > 0` and `x > 0`,
`P(sup_{t≥0} (A_o(t) − μ_A t − ν t) ≥ x)` (9) equals
`P(sup_{k≥0} (μ_A/(μ_A+ν) k − Σ_{i=1}^k μ_A A_i) ≥ x (1 + ν/μ_A)⁻¹)` (10). -/
theorem lemma_8 (μA : Measure ℝ) [IsProbabilityMeasure μA] (hA : IsTimeLaw μA)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : IsIIDSeq P X μA) (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    P.real {ω | (x : EReal) ≤
        supFrom (fun t => (ordCount (fun j => X j ω) t : ℝ) - rate μA * t - ν * t)} =
      P.real {ω | ((x * (1 + ν / rate μA)⁻¹ : ℝ) : EReal) ≤
        ⨆ k : ℕ, ((rate μA / (rate μA + ν) * k - ∑ i ∈ Finset.range k, rate μA * X i ω : ℝ) : EReal)} := by sorry

end GIGnBounds.Tail

-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_3
-- name    : GIGnBounds.Tail.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:07.375508+00:00
-- url     : https://prove2.me/theorems/59a25fbc-55c3-4131-8ddf-913e55ae880f
-- title:
--   Lemma 3 — $P(\sup_t(A_o(t)-\mu_At-\nu t)\ge x)\le\exp(-.09\frac{\nu}{\nu+\mu_A}(E[(A\mu_A)^2])^{-1}x)$
-- statement:
--   Let $\mathcal A_o$ be an ordinary renewal process with i.i.d. inter-event times of law $\mu_A$ (nonnegative, finite positive mean, rate $\mu_A$), $A_o(t)$ its number of renewals in $[0,t]$, and suppose $\mathbb E[A^2]<\infty$.
--
--   **Lemma 3.** For all $\nu>0$ and $x>0$,
--
--   $$\mathbb P\Big(\sup_{t\ge0}\big(A_o(t)-\mu_At-\nu t\big)\ge x\Big)\le\exp\Big(-.09\,\frac{\nu}{\nu+\mu_A}\,\big(\mathbb E[(A\mu_A)^2]\big)^{-1}x\Big).$$
--
--   This bounds the arrival supremum (5) of Lemma 2 with $\nu=\tfrac12(n-\mu_A)$.
--
--   **Formalization Note.** $.09$ is written $9/100$. $\mathbb E[(A\mu_A)^2]$ is a real integral, finite under the hypothesis $\mathbb E[A^2]<\infty$.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 25, Lemma 3

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 3** (Li–Goldberg, arXiv:1706.04628v3, p. 25). If `E[A²] < ∞`, then for the ordinary renewal
process `A_o` with i.i.d. intervals of law `μA` (here `X 0, X 1, …`), for all `ν > 0` and `x > 0`,
`P(sup_{t≥0} (A_o(t) − μ_A t − ν t) ≥ x) ≤ exp(−.09 (ν/(ν+μ_A)) (E[(A μ_A)²])⁻¹ x)`. -/
theorem lemma_3 (μA : Measure ℝ) [IsProbabilityMeasure μA] (hA : IsTimeLaw μA)
    (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : IsIIDSeq P X μA) (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    P.real {ω | (x : EReal) ≤
        supFrom (fun t => (ordCount (fun j => X j ω) t : ℝ) - rate μA * t - ν * t)} ≤
      Real.exp (-((9 : ℝ) / 100) * (ν / (ν + rate μA)) * (nMoment μA 2)⁻¹ * x) := by sorry

end GIGnBounds.Tail

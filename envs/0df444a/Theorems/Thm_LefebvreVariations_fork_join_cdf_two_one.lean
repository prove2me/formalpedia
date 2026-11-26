-- Prove2me | Theorems.Thm_LefebvreVariations_fork_join_cdf_two_one
-- name    : LefebvreVariations.fork_join_cdf_two_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:27:58.840803+00:00
-- url     : https://prove2.me/theorems/c33172e8-d0a6-492e-823e-ad4c0b8c87c9
-- title:
--   Lefebvre's variations, No. 208 — on a theme by Carmeli, Yom-Tov and Boxma: the fork-join sojourn law with two exponential services at one station and one at the other
-- statement:
--   Let $U_0,U_1,\dots$ and $G_0,G_1,\dots$ be mutually independent exponential service times with rates $\mu_1,\mu_2>0$ respectively, and put $S_1=U_0+U_1$, $S_2=G_0$. Then $S_1\sim\mathrm{Gamma}(2,\mu_1)$, $S_2\sim\mathrm{Gamma}(1,\mu_2)$ and for every $t\ge0$
--   $$\mathbb{P}\bigl(\max(S_1,S_2)\le t\bigr)=\mathbb{P}(S_1\le t)\,\mathbb{P}(S_2\le t)=\bigl(1-e^{-\mu_1t}(1+\mu_1t)\bigr)\bigl(1-e^{-\mu_2t}\bigr).$$
--
--   This is the sojourn-time law of a customer in a two-station fork-join network who finds one customer ahead at the first station and none at the second; the same product is the CDF of the maximum under the product of the two gamma laws.
--
--   **Formalization Note** The statement is the full six-part conclusion of `ForkJoinDelay.sec_3_1_fj_cdf` with the hypotheses `x = 2` and `y = 1` added; Mathlib's `gammaMeasure a r` has shape `a` and rate `r`, and the displayed sums `∑ m ∈ Finset.range x …` are kept as in the parent (for `x = 2`, `y = 1` they give `e^{-µ₁t}(1+µ₁t)` and `e^{-µ₂t}`). The family `![U, G]` is jointly independent (`iIndepFun` over `Fin 2 × ℕ`), and `t ≥ 0`.
--
--   **Why this is a variation.** Variation of the open platform problem ForkJoinDelay.sec_3_1_fj_cdf (gamma sojourn laws and the fork-join CDF for x and y customers ahead). It is the first case with a genuine sum, x=2 and y=1, in the parent's own statement. It is the parent with those values substituted, hence a consequence of the parent (no formal import).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: ForkJoinDelay.sec_3_1_fj_cdf (platform, Open), Section 3.1 of N. Carmeli, G. B. Yom-Tov and O. J. Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, Manufacturing & Service Operations Management 25(3) (2023) 1081-1098 (paper and authors verified online; section and page numbers taken from the parent's source field, not checked). The Erlang(2) CDF 1 - e^{-mu t}(1+mu t) is elementary; at t=0 both sides are 0 (Lean convention 0^0 = 1). Monte Carlo check in python3 (mu1=1.3, mu2=0.7, t=1.9, 400000 draws): 0.51929 vs formula 0.51964.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory

/-- The case `x = 2`, `y = 1` of `ForkJoinDelay.sec_3_1_fj_cdf`: the upper station sojourn is `Gamma(2, µ₁)` (sum of two
exponential services), the lower one `Gamma(1, µ₂) = Exp(µ₂)`, and the fork-join CDF is
`(1 - e^{-µ₁ t}(1 + µ₁ t)) (1 - e^{-µ₂ t})`.
Source: Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join Networks*, §3.1 (as quoted on the platform);
the Erlang CDF is elementary. -/
theorem fork_join_cdf_two_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₁ μ₂ : ℝ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (U G : ℕ → Ω → ℝ)
    (hU : ∀ n, Measurable (U n)) (hG : ∀ n, Measurable (G n))
    (hind : iIndepFun (fun i : Fin 2 × ℕ => ![U, G] i.1 i.2) P)
    (hlawU : ∀ n, P.map (U n) = expMeasure μ₁) (hlawG : ∀ n, P.map (G n) = expMeasure μ₂)
    (x y : ℕ) (hx : x = 2) (hy : y = 1) (t : ℝ) (ht : 0 ≤ t) :
    P.map (fun ω => ∑ i ∈ Finset.range x, U i ω) = gammaMeasure (x : ℝ) μ₁ ∧
    P.map (fun ω => ∑ i ∈ Finset.range y, G i ω) = gammaMeasure (y : ℝ) μ₂ ∧
    (P {ω | max (∑ i ∈ Finset.range x, U i ω) (∑ i ∈ Finset.range y, G i ω) ≤ t}).toReal =
      (P {ω | ∑ i ∈ Finset.range x, U i ω ≤ t}).toReal *
        (P {ω | ∑ i ∈ Finset.range y, G i ω ≤ t}).toReal ∧
    (P {ω | ∑ i ∈ Finset.range x, U i ω ≤ t}).toReal =
      1 - ∑ m ∈ Finset.range x, Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ m / (m.factorial : ℝ) ∧
    (P {ω | ∑ i ∈ Finset.range y, G i ω ≤ t}).toReal =
      1 - ∑ n ∈ Finset.range y, Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ n / (n.factorial : ℝ) ∧
    (((gammaMeasure (x : ℝ) μ₁).prod (gammaMeasure (y : ℝ) μ₂))
        {p : ℝ × ℝ | max p.1 p.2 ≤ t}).toReal =
      (1 - ∑ m ∈ Finset.range x, Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ m / (m.factorial : ℝ)) *
        (1 - ∑ n ∈ Finset.range y, Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ n / (n.factorial : ℝ)) := by
  sorry

end LefebvreVariations

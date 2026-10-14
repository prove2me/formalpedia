-- Prove2me | Theorems.Thm_GIGnBounds_Tail_sup_bound_r_gt_2_5
-- name    : GIGnBounds.Tail.sup_bound_r_gt_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:18.706242+00:00
-- url     : https://prove2.me/theorems/aef84a96-03e8-4f4b-87a7-cdc2377874fb
-- title:
--   Display p. 28 — for $x\ge18$, $r\in(2.5,r^*)$, explicit bound on (4) with $((1-\rho)x)^{-r/2}$
-- statement:
--   Let $\mathbb E[S]=1$, let $n\ge1$ be an integer with $n>\mu_A$, so that $\rho=\mu_A/n<1$, and let $\mathbb E[A^2]<\infty$. Here $(\Omega,\mathcal F,\mathbb P)$ is any probability space carrying a **bounding family**: an equilibrium renewal process $\mathcal A_e$ with renewals distributed as $A$ (first interval distributed as $R(A)$), and $n$ equilibrium renewal processes $\mathcal N_{e,1},\dots,\mathcal N_{e,n}$ with renewals distributed as $S$ (first interval $R(S)$), all intervals of all processes mutually independent. $A_e(t)$ and $N_{e,i}(t)$ are their numbers of renewals in $[0,t]$.
--
--   **Display (proof of the bounds for $L(\infty)$ in Theorems 1–2, p. 28).** For $x\ge18$ and $r\in(2.5,r^*)$, $\mathbb P\big(\sup_{t\ge0}(A_e(t)-\sum_{i=1}^nN_{e,i}(t))\ge x\big)$ is at most
--
--   $$1.3\times10^4\,(\mathbb E[S^2]+1)\,(4.6\times10^5)^r\Big((\mathbb E[S^2]+1)^{r-1}r^{2.5r}+r^{1.5r}\,\mathbb E[S^r]\Big)\big((1-\rho)x\big)^{-\frac r2}+1.1\exp\Big(-.0225\big(\mathbb E[(A\mu_A)^2]\big)^{-1}(1-\rho)x\Big).$$
--
--   This is the bound on the bounding process from which both parts of Theorem 2 follow (for $L(\infty)$ via Lemma 1, for the s.s.p.d. via Corollary 5 with $n'$ servers).
--
--   **Formalization Note.** $1.3\times10^4$ is $13\cdot10^3$ and $4.6\times10^5$ is $46\cdot10^4$. $\mathbb E[S^r]$ is finite because $r<r^*$.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, proof of the bounds for L(∞) in Theorems 1 – 2, p. 28, "for x ≥ 18 and r ∈ (2.5, r∗), (4) is at most"

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Display, p. 28** (proof of the bounds for `L(∞)` in Theorems 1–2, Li–Goldberg,
arXiv:1706.04628v3). Let `E[S] = 1`, `n ≥ 1` with `n > μ_A`, and `E[A²] < ∞`. For `x ≥ 18` and
`r ∈ (2.5, r*)`, the supremum (4) is at most the explicit bound below, with `ρ = μ_A / n`. -/
theorem sup_bound_r_gt_2_5 (n : ℕ) (hn : 1 ≤ n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hstab : rate μA < n) (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (r : ℝ) (hr₁ : (5 : ℝ) / 2 < r) (hr₂ : (r : EReal) < rStar μS)
    (x : ℝ) (hx : 18 ≤ x) :
    P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} ≤
      13 * 10 ^ 3 * (∫ y, y ^ 2 ∂μS + 1) * ((46 : ℝ) * 10 ^ 4) ^ r *
          ((∫ y, y ^ 2 ∂μS + 1) ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) +
            r ^ ((3 : ℝ) / 2 * r) * ∫ y, y ^ r ∂μS) *
          ((1 - rho n μA μS) * x) ^ (-(r / 2)) +
        11 / 10 * Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * ((1 - rho n μA μS) * x)) := by sorry

end GIGnBounds.Tail

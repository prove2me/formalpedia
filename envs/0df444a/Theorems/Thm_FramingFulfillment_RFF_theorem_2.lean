-- Prove2me | Theorems.Thm_FramingFulfillment_RFF_theorem_2
-- name    : FramingFulfillment.RFF.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:44.462825+00:00
-- url     : https://prove2.me/theorems/05b6cdff-a78a-47a0-bd0c-dea67aa669e1
-- title:
--   Theorem 2, p. 23 — RFF is within M√θ of the deterministic bound 𝒥^D(θ), and 1 − 𝒥^RFF(θ)/𝒥*(θ) = O(θ^{-1/2})
-- statement:
--   Consider a JFF instance satisfying the standing assumptions, and scale it by $\theta\in\mathbb N$: horizon $\theta T$, inventories $\theta C$. Let $\mathcal J^D(\theta)$ be the optimal value of DET' and $\mathcal J^*(\theta)$ the optimal expected profit. Let $\mathcal J^{RFF}(\theta)$ be the expected total profit of the Randomized Framing and Fulfillment policy built from an optimal DET' solution $(x^{t,D},y^{t,D})$ and from framing decompositions of the matrices $B(x^{t,D}_j)$ used by ConstrDist. Then:
--
--   1. there are $M>0$ and $\theta_0$ such that for every $\theta\ge\theta_0$, DET'$(\theta)$ has an optimal solution and, for **every** optimal solution and **every** choice of decompositions,
--   $$0\le\mathcal J^D(\theta)-\mathcal J^{RFF}(\theta)\le M\sqrt\theta;$$
--   2. if $\mathcal J^*(1)>0$, there are $M'$ and $\theta_1$ such that for every $\theta\ge\theta_1$, $\mathcal J^*(\theta)>0$ and, for every optimal solution and every choice of decompositions,
--   $$\Big|1-\frac{\mathcal J^{RFF}(\theta)}{\mathcal J^*(\theta)}\Big|\le\frac{M'}{\sqrt\theta}.$$
--
--   The constants depend on the instance only, not on $\theta$, the optimal solution or the decompositions. So RFF is asymptotically optimal: its relative loss against the best policy vanishes at rate $\theta^{-1/2}$.
--
--   **Formalization Note**
--   - **The policy.** $\mathcal J^{RFF}$ is the exact expected profit of RFF as defined on p. 23, including its stock-out handling: products out of stock everywhere are hidden, and orders are re-routed to the cheapest FC with stock, ties broken by least index. It is not the value of an idealized policy that ignores stock-outs.
--   - **"For all large $\theta$" and "independent of $\theta$".** These are rendered as $\exists M\,\exists\theta_0\,\forall\theta\ge\theta_0$. Uniformity over optimal solutions and decompositions is implicit on the page, where $\mathcal J^{RFF}$ is written as a function of $\theta$ alone. "$O(\theta^{-1/2})$" is rendered as an absolute-value bound $M'/\sqrt\theta$.
--   - **Hypotheses added relative to the page.** These are the model's standing assumptions: $\sum_j\lambda_j\le1$, $v_{ijR}=0<v_{ijr}$ for $r\ne R$, $Q_R\ge I$, $\theta\in\mathbb N$, and the FC set $[K]$.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), p. 23, Theorem 2 (RFF policy box, p. 23; printed proof Electronic Companion EC 2–EC 3, PDF 35–36)

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

namespace FramingFulfillment.RFF

/-- Theorem 2 (p. 23). There is `M > 0` independent of `θ` such that for all large `θ`,
DET'(θ) has an optimal solution and, for every optimal solution `s` and every choice of
framing decompositions used by ConstrDist, `0 ≤ 𝒥^D(θ) − 𝒥^RFF(θ) ≤ M √θ`. Moreover, if
`𝒥*(1) > 0`, then `1 − 𝒥^RFF(θ)/𝒥*(θ) = O(θ^{-1/2})`. -/
theorem theorem_2 (P : Inst) (hP : P.Standing) :
    (∃ M : ℝ, 0 < M ∧ ∃ θ₀ : ℕ, ∀ θ : ℕ, θ₀ ≤ θ →
      (∃ s, (P.scale θ).IsDETOpt s) ∧
      ∀ s, (P.scale θ).IsDETOpt s →
        ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
          0 ≤ (P.scale θ).JD - (P.scale θ).JRFF s dec ∧
          (P.scale θ).JD - (P.scale θ).JRFF s dec ≤ M * Real.sqrt (θ : ℝ)) ∧
    (0 < (P.scale 1).Jstar →
      ∃ M' : ℝ, ∃ θ₁ : ℕ, ∀ θ : ℕ, θ₁ ≤ θ →
        0 < (P.scale θ).Jstar ∧
        ∀ s, (P.scale θ).IsDETOpt s →
          ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
            |1 - (P.scale θ).JRFF s dec / (P.scale θ).Jstar| ≤ M' / Real.sqrt (θ : ℝ)) := by sorry

end FramingFulfillment.RFF

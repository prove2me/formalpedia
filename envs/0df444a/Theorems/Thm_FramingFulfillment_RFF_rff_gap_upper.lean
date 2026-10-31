-- Prove2me | Theorems.Thm_FramingFulfillment_RFF_rff_gap_upper
-- name    : FramingFulfillment.RFF.rff_gap_upper
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T15:19:48.041631+00:00
-- url     : https://prove2.me/theorems/6aad9eea-28fd-48f1-b1fb-715fbccd602d
-- title:
--   Theorem 2 (upper bound, EC 2) — 𝒥^D(θ) − 𝒥^RFF(θ) ≤ M√θ for all large θ
-- statement:
--   Consider a JFF instance satisfying the standing assumptions, scaled by $\theta\in\mathbb N$ (horizon $\theta T$, inventories $\theta C$). Let $\mathcal J^D(\theta)$ be the optimal value of DET' and let $\mathcal J^{RFF}(\theta)$ be the exact expected profit of the Randomized Framing and Fulfillment policy of p. 23. The policy is built from an optimal DET' solution $(x^{t,D},y^{t,D})$ and from framing decompositions of the matrices $B(x^{t,D}_j)$ used by ConstrDist, and it includes the policy's stock-out handling (hiding products that are out of stock everywhere, re-routing orders to the cheapest FC with stock).
--
--   **Claim.** There are a constant $M>0$ and a threshold $\theta_0$, depending only on the instance, such that for every $\theta\ge\theta_0$, every optimal DET' solution and every choice of decompositions,
--   $$\mathcal J^D(\theta)-\mathcal J^{RFF}(\theta)\le M\sqrt\theta .$$
--
--   This is the upper half of Theorem 2, part 1. The source's proof (EC 2) compares RFF with a variant that ignores stock-outs and pays a penalty $\bar c$ per unit of excess demand. It then bounds the expected excess $\mathbb E[(\sum_t Y^t_{ijk}-C_{ik}(\theta))^+]$ by $\sqrt{\mathrm{Var}}=O(\sqrt\theta)$, using Lemma 3. The constant is left existential here: with hiding and re-routing, one stock-out can push extra demand onto other products and FCs, so the explicit constant $\bar c\,IJK\sqrt T$ of EC 2 is not claimed.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), p. 23, Theorem 2 (upper bound in part 1); proof in Electronic Companion EC 2 (PDF pp. 35–36), inequality chain after (EC.4)

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

namespace FramingFulfillment.RFF

theorem rff_gap_upper (P : Inst) (hP : P.Standing) :
    ∃ M : ℝ, 0 < M ∧ ∃ θ₀ : ℕ, ∀ θ : ℕ, θ₀ ≤ θ →
      ∀ s, (P.scale θ).IsDETOpt s →
        ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
          (P.scale θ).JD - (P.scale θ).JRFF s dec ≤ M * Real.sqrt (θ : ℝ) := by sorry

end FramingFulfillment.RFF

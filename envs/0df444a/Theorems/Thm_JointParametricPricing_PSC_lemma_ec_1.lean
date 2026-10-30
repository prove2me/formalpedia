-- Prove2me | Theorems.Thm_JointParametricPricing_PSC_lemma_ec_1
-- name    : JointParametricPricing.PSC.lemma_ec_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:49:14.512997+00:00
-- url     : https://prove2.me/theorems/1d53b3c2-5abb-474b-94f9-32b0bbeecbd7
-- title:
--   Lemma EC.1 — local optimizer stability and binding dual support
-- statement:
--   Fix the general pricing model satisfying A1–A6, with positive interior-price radius $\varphi$. There exist $\kappa>0$ and $\bar\delta>0$, independent of scaling, such that for every $\theta\in\Theta\cap\operatorname{Ball}(\theta^*,\bar\delta)$,
--   $$p^D(\theta)\in\operatorname{Ball}(p^D(\theta^*),\varphi/2),\qquad \operatorname{Ball}(p^D(\theta),\varphi/2)\subseteq P,$$
--   $$\|\lambda^D(\theta^*)-\lambda^D(\theta)\|_2\le\kappa\|\theta^*-\theta\|_2.$$
--   Moreover, for each such $\theta$ there exists an optimal dual solution $\mu^D(\theta^*)$ of the true capacity program with
--   $$A_i\lambda^D(\theta)=C_i\quad\text{for every }i\text{ with }\mu_i^D(\theta^*)>0.$$
--   The dual witness may depend on the nearby parameter. Balls are closed. The last equality is the printed, unnormalized equality, including its discrepancy with the capacity $C/T$ (I1).
--
--   Differences from the source:
--   - encoding: positive finite dimensions, Euclidean norms, and parameters in Θ → Fin indices, EuclideanSpace vectors, and the subtype Θ; reason: preserves the full continuous domains and the source 2-norms
--   - encoding: C² or C¹ functions on the stated compact domains → local ambient smooth representatives at domain points, with coordinate derivatives; reason: implements the usual smooth-on-a-compact-domain convention without imposing global smoothness or any new uniform exterior bound
--   - encoding: the deterministic T-period program and its optimal rate and dual → the attained constant-rate program with capacity C/T and its true Lagrange dual; reason: convexity of the rate image and concavity of revenue give the equivalent constant-rate program; the printed C equalities remain unchanged
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); Lemma EC.1, printed ec2 / PDF 26

import Definitions.Def_JointParametricPricing_PSC_Exploration

open scoped BigOperators

namespace JointParametricPricing.PSC

theorem lemma_ec_1 {n m q : ℕ} (M : Model n m q) (hf : M.Feasible)
    (E : ExplorationPrices M) (hA5 : E.A5) (φ : ℝ) (hA6 : M.A6 hf φ) :
    ∃ κ δbar : ℝ, 0 < κ ∧ 0 < δbar ∧ ∀ θ : M.Θ,
      (θ : Vec q) ∈ Metric.closedBall M.thetaStar δbar →
      M.optimalPrice hf θ ∈ Metric.closedBall (M.optimalPrice hf ⟨M.thetaStar, M.thetaStar_mem⟩) (φ / 2) ∧
      Metric.closedBall (M.optimalPrice hf θ) (φ / 2) ⊆ M.prices ∧
      ‖M.optimalRate hf ⟨M.thetaStar, M.thetaStar_mem⟩ - M.optimalRate hf θ‖ ≤
        κ * ‖M.thetaStar - θ‖ ∧
      ∃ μ : Fin m → ℝ, (M.program M.thetaStar).IsDualOptimum μ ∧
        ∀ i, 0 < μ i → (M.program θ).load (M.optimalRate hf θ) i = M.C i := by sorry

end JointParametricPricing.PSC

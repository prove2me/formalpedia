-- Prove2me | Theorems.Thm_JointParametricPricing_PSC_claim_ec_1
-- name    : JointParametricPricing.PSC.claim_ec_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:48:52.558932+00:00
-- url     : https://prove2.me/theorems/903a453a-ce11-4722-bee0-f617111618bf
-- title:
--   Claim EC.1 — nearby printed KKT solutions with independent positive support
-- statement:
--   Under the A1–A6 model and the context of Lemma EC.1, there exists $\delta_3>0$ such that every $\theta\in\Theta\cap\operatorname{Ball}(\theta^*,\delta_3)$ has a nonnegative multiplier $\mu$ satisfying the printed KKT equations
--   $$\nabla_x r(\lambda^D(\theta);\theta)=A^\top\mu,\qquad \mu_i(A_i\lambda^D(\theta)-C_i)=0.$$
--   Its positive support is contained in $B^*=\{i:A_i\lambda^D(\theta^*)=C_i\}$, and the rows $A_i$ indexed by that support are linearly independent. These printed equations are kept distinct from the actual program's dual; their unnormalized capacities remain as printed (I1).
--
--   Differences from the source:
--   - encoding: positive finite dimensions, Euclidean norms, and parameters in Θ → Fin indices, EuclideanSpace vectors, and the subtype Θ; reason: preserves the full continuous domains and the source 2-norms
--   - encoding: C² or C¹ functions on the stated compact domains → local ambient smooth representatives at domain points, with coordinate derivatives; reason: implements the usual smooth-on-a-compact-domain convention without imposing global smoothness or any new uniform exterior bound
--   - encoding: the deterministic T-period program and its optimal rate and dual → the attained constant-rate program with capacity C/T and its true Lagrange dual; reason: convexity of the rate image and concavity of revenue give the equivalent constant-rate program; the printed C equalities remain unchanged
--   - reading: some constant δ₃ in the claim, with δ₃∈(0,δ₁] in the proof → δ₃>0; reason: the proof specifies a positive radius, excluding an empty-ball reading
--   - reading: the proof writes a complement indexed through n → resources are indexed through m; reason: A has m resource rows; the claim concerns those rows
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); Claim EC.1, printed ec3 / PDF 27

import Definitions.Def_JointParametricPricing_PSC_Exploration

namespace JointParametricPricing.PSC

theorem claim_ec_1 {n m q : ℕ} (M : Model n m q) (hf : M.Feasible)
    (E : ExplorationPrices M) (hA5 : E.A5) (φ : ℝ) (hA6 : M.A6 hf φ) :
    ∃ δ₃ : ℝ, 0 < δ₃ ∧ ∀ θ : M.Θ,
      (θ : Vec q) ∈ Metric.closedBall M.thetaStar δ₃ →
      ∃ μ : Fin m → ℝ, M.printedKKT hf θ μ ∧
        {i | 0 < μ i} ⊆ M.printedActive hf ∧
        LinearIndependent ℝ (fun i : {i : Fin m // 0 < μ i} => M.A i.val) := by sorry

end JointParametricPricing.PSC

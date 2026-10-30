-- Prove2me | Theorems.Thm_JointParametricPricing_PSC_theorem_1
-- name    : JointParametricPricing.PSC.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:50:14.306062+00:00
-- url     : https://prove2.me/theorems/ebfb4c8f-dc4d-4817-994f-152a35eb92f7
-- title:
--   Theorem 1 — rate-optimal regret of PSC
-- statement:
--   Fix any general parametric network pricing model satisfying A1–A6, with arbitrary positive finite product, resource, and parameter dimensions and positive integer base horizon $T$. Ordinary prices range over the entire compact box, demand permits substitution, and the compact parameter set need not be convex. Fix any history-based maximizing MLE selector. In the $k$th system, use PSC with initial stock $kC$, horizon $kT$, and $L(k)=\lceil\sqrt{kT}\rceil$. Then
--   $$\exists M_1>0\;\forall k\in\mathbb Z_{\ge1}:\quad \rho^{\mathrm{PSC}}(k)\le M_1\sqrt k.$$
--   Here $\rho^{\mathrm{PSC}}(k)=kT r(\lambda^D(\theta^*);\theta^*)-E_{\theta^*}^{\mathrm{PSC}}[\text{total realized revenue}]$. The expectation is under the recursively induced categorical sales law. PSC includes the stated exploration shutdown, one MLE and deterministic optimization, equation (1)'s rate adjustments, the inverse-domain feasibility check, and productwise previous-price fallback. The single constant is chosen before $k$; early termination and the whole small-horizon prefix remain included. No lower-bound or APSC assertion is added.
--
--   Differences from the source:
--   - encoding: positive finite dimensions, Euclidean norms, and parameters in Θ → Fin indices, EuclideanSpace vectors, and the subtype Θ; reason: preserves the full continuous domains and the source 2-norms
--   - encoding: C² or C¹ functions on the stated compact domains → local ambient smooth representatives at domain points, with coordinate derivatives; reason: implements the usual smooth-on-a-compact-domain convention without imposing global smoothness or any new uniform exterior bound
--   - encoding: the deterministic T-period program and its optimal rate and dual → the attained constant-rate program with capacity C/T and its true Lagrange dual; reason: convexity of the rate image and concavity of revenue give the equivalent constant-rate program; the printed C equalities remain unchanged
--   - encoding: any maximum-likelihood maximizer → a fixed selector over observation strings with its exact likelihood-maximization property; reason: keeps all ties and derives the probability from the actual experiment; no concentration property is assumed
--   - encoding: adaptive stochastic sales and total expected revenue → a finite-history recursion and its exact finite path sum; reason: preserves every categorical outcome and continuous price decision without asserting unconditional independence
--   - reading: apply the inverse and check that the candidate price lies in P → return no candidate when the target is outside Λ of the estimated parameter; reason: the inverse is specified only on Λ; this is the infeasible-price branch, not a projection
--   - reading: turn product j off if C_(t-1)≺A_j → turn it off if remaining capacity does not dominate A_j; reason: the printed strict comparison contradicts the stock-insufficiency safeguard; I4 records the explicit positive-probability path
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); Theorem 1, printed 12 / PDF 13

import Definitions.Def_JointParametricPricing_PSC_Policy

namespace JointParametricPricing.PSC

theorem theorem_1 {n m q : ℕ} (M : Model n m q) (hf : M.Feasible)
    (E : ExplorationPrices M) (hA5 : E.A5) (φ : ℝ) (hA6 : M.A6 hf φ)
    (S : E.MLESelector) :
    ∃ M₁ : ℝ, 0 < M₁ ∧ ∀ k : ℕ, 1 ≤ k → M.regret hf E S k ≤ M₁ * Real.sqrt k := by sorry

end JointParametricPricing.PSC

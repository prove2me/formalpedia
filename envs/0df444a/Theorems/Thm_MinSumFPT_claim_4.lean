-- Prove2me | Theorems.Thm_MinSumFPT_claim_4
-- name    : MinSumFPT.claim_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:56.444068+00:00
-- url     : https://prove2.me/theorems/573438c3-59e6-4f19-97cc-d19d09f8b154
-- title:
--   Claim 4 — an approximate center is close to $\mu_C$
-- statement:
--   Let $d$ be a pseudometric on $A$, $C$ a nonempty cluster and $\mathrm{OPT}=\mathrm{OPT}_k(d)$. If $p$ is an $(\varepsilon,\alpha)$-approximate center of $C$ (Eq. (1)), then
--
--   $$
--   \|e_p-\mu_C\|_{W_1}\le\frac{\varepsilon}{4\alpha}\cdot\frac{\mathrm{OPT}}{k\cdot|C|^2}+\alpha\cdot\Delta_C .
--   $$
--
--   Claim 4 converts the covering condition (1), a statement about the sum of distances to $p$, into a bound on the distance from $p$ to the cluster's center. Stages 2 and 3 use it to locate the points of each cluster around its approximate center.
--
--   Differences from the source:
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
--   - encoding: a cluster C → a nonempty Finset C; reason: µ_C and Δ_C divide by |C|; excludes only undefined cases
--   - generalization: ε > 0, α > 0 (implicit) → all real ε, α; reason: the claim is (1) divided by |C|², valid for every ε, α
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Claim 4, p.9

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_IsCovered

namespace MinSumFPT

/-- Claim 4 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Claim 4, p.9): if `p` is an (ε, α)-approximate center of a nonempty
cluster `C` (Eq. (1) with OPT the optimal k-minsum cost), then
`‖e_p − µ_C‖_{W₁} ≤ (ε/(4α)) ⋅ OPT/(k ⋅ |C|²) + α ⋅ Δ_C`.

**Formalization Note.** Stated for all real `ε, α` (the paper's are positive); the claim is the
division of (1) by `|C|²`. -/
theorem claim_4 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsPseudometric d) (k : ℕ)
    (ε α : ℝ) (C : Finset (Fin n)) (hC : C.Nonempty) (p : Fin n)
    (hp : IsApproxCenter d (optCost d k) k ε α C p) :
    PerturbedWF.transNorm d (unitVec p - centroid C) ≤
      ε / (4 * α) * (optCost d k / (k * (C.card : ℝ) ^ 2)) + α * Delta d C := by sorry

end MinSumFPT

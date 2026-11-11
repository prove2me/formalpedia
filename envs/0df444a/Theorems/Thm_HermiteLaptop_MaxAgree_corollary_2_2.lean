-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_corollary_2_2
-- name    : HermiteLaptop.MaxAgree.corollary_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:39.997739+00:00
-- url     : https://prove2.me/theorems/82b94300-2e70-4e34-93be-bf6735527305
-- title:
--   Corollary 2.2 — (1 − P(ρ))/(1 − ρ) is nondecreasing on [−1/2, 1) for every mixture of k-spokes roundings
-- statement:
--   Let $\mathcal K$ be a set of positive integers and $\lambda=(\lambda_k)_{k\in\mathcal K}$ with $\lambda_k\ge0$ and $\sum_{k\in\mathcal K}\lambda_k=1$. Let $P(\rho)$ be the probability that the mixture of the $k$-spokes roundings with probabilities $\lambda$ puts two unit vectors with inner product $\rho$ in the same cluster, and $R(\rho)=(1-P(\rho))/(1-\rho)$ for $\rho\in[-1,1)$. Then $R$ is nondecreasing on $[-1/2,1)$.
--
--   **Formalization Note.** The mixture is a `Mixture` and $P$ is `Mixture.collision`, $\sum_k\lambda_kP_k(\rho)$.
--
--   Differences from the source:
--   - encoding: P(ρ) = the probability that the mixture assigns i and j to the same cluster → Mixture.collision ρ = Σ_k λ_k P_k(ρ), λ : ℕ → ℝ zero off K with HasSum λ 1; reason: law of total probability; K may be infinite
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 15 (PDF 18), Corollary 2.2

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Mixture

namespace HermiteLaptop.MaxAgree

/-- Corollary 2.2: for every mixture of k-spokes roundings, `R(ρ) = (1 − P(ρ))/(1 − ρ)` is
nondecreasing on `[−1/2, 1)`. -/
theorem corollary_2_2 (μ : Mixture) :
    MonotoneOn (fun ρ : ℝ => (1 - μ.collision ρ) / (1 - ρ)) (Set.Ico (-1 / 2 : ℝ) 1) := by sorry

end HermiteLaptop.MaxAgree

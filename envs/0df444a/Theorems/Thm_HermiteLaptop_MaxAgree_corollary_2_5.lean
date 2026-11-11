-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_corollary_2_5
-- name    : HermiteLaptop.MaxAgree.corollary_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:18:19.500098+00:00
-- url     : https://prove2.me/theorems/b4663bb8-31b9-4852-b922-3e9db510b1aa
-- title:
--   Corollary 2.5 — the two-sided bound P̲_M(ρ) ≤ P(ρ) ≤ P̄_M(ρ) for every mixture
-- statement:
--   Fix $M\in\mathbb N_0$ and a mixture of $k$-spokes roundings as in Corollary 2.2. Suppose that for each $k\in\mathcal K$ and $m=0,\dots,M$ we have bounds $\underline c_{k,m}\le c_{k,m}\le\overline c_{k,m}$, and put $\underline P_M(\rho)=\sum_{k\in\mathcal K}\lambda_k\underline P_{k,M}(\rho)$, $\overline P_M(\rho)=\sum_{k\in\mathcal K}\lambda_k\overline P_{k,M}(\rho)$. Then
--   $$\underline P_M(\rho)\le P(\rho)\le\overline P_M(\rho)\qquad\text{for all }\rho\in[-1,1].$$
--
--   **Formalization Note.** The two defining series are assumed summable on $[-1,1]$.
--
--   Differences from the source:
--   - encoding: P̲_M = Σ_{k∈K} λ_k P̲_{k,M}, P̄_M = Σ_{k∈K} λ_k P̄_{k,M} (series over a possibly infinite K) → hypotheses that both series are summable on [−1, 1]; reason: for arbitrary bounds the printed series may diverge and P̲_M, P̄_M are then undefined; the hypothesis excludes only that case (automatic for finite K)
--   - encoding: mixture probabilities (λ_k)_{k∈K} and its collision probability P → Mixture with λ : ℕ → ℝ zero off K, HasSum λ 1, P = Σ_k λ_k P_k; reason: law of total probability; K may be infinite
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), pp. 17–18 (PDF 20–21), Corollary 2.5

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite
import Definitions.Def_HermiteLaptop_MaxAgree_TruncBounds

namespace HermiteLaptop.MaxAgree

/-- Corollary 2.5: for a mixture and bounds `c̲_{k,m} ≤ c_{k,m} ≤ c̄_{k,m}` (`k ∈ K`, `m ≤ M`),
`P̲_M(ρ) ≤ P(ρ) ≤ P̄_M(ρ)` on `[−1, 1]`, where `P̲_M = Σ λ_k P̲_{k,M}`, `P̄_M = Σ λ_k P̄_{k,M}`
(the two series are assumed to converge). -/
theorem corollary_2_5 (M : ℕ) (μ : Mixture) (cl cu : ℕ → ℕ → ℝ)
    (hcl : ∀ k ∈ μ.K, ∀ m ≤ M, cl k m ≤ coeffC k m)
    (hcu : ∀ k ∈ μ.K, ∀ m ≤ M, coeffC k m ≤ cu k m)
    (hsumL : ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      Summable (fun k : ℕ => μ.lam k * truncLower M (cl k) (cu k) ρ))
    (hsumU : ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      Summable (fun k : ℕ => μ.lam k * truncUpper M (cl k) (cu k) ρ)) :
    ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      μ.truncLower M cl cu ρ ≤ μ.collision ρ ∧ μ.collision ρ ≤ μ.truncUpper M cl cu ρ := by sorry

end HermiteLaptop.MaxAgree

-- Prove2me | Theorems.Thm_ImpliedAmbiguity_Supplement_theorem_1
-- name    : ImpliedAmbiguity.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:02:49.612907+00:00
-- url     : https://prove2.me/theorems/d235bd79-0be9-45db-8a0a-da05b99947f4
-- title:
--   Theorem 1 (Optimal portfolio in terms of basis portfolios) — $\zeta(\eta)=\sum_k v_k/(1+\lambda_k\eta)$ for eigenvectors $v_k$ of $Q$
-- statement:
--   Let $\Sigma_R \in \mathcal S^N_{++}$ be a symmetric positive definite covariance matrix and let $\Sigma_M$ be a second-order belief with $0 \le \Sigma_M \le \Sigma_R$ in the Loewner order ($A \le B$ means $B - A$ is positive semidefinite). Let $\mu \in \mathbb R^N$ be the vector of expected returns and $R_f \in \mathbb R$ the risk-free return, write $Q = \Sigma_R^{-1}\Sigma_M$, and let $\zeta(\eta) = (I+\eta Q)^{-1}\Sigma_R^{-1}(\mu - R_f\mathbf 1)$ as in (10).
--
--   Suppose that $\mu - R_f\mathbf 1 \neq 0$. Then there are a positive integer $K$, nonzero vectors $v_1,\dots,v_K \in \mathbb R^N$ and pairwise distinct real numbers $\lambda_1,\dots,\lambda_K$ with $Q v_k = \lambda_k v_k$ for every $k$, such that, for every $\eta > -1$,
--
--   $$
--   \zeta(\eta) = \sum_{k=1}^{K} \frac{1}{1+\lambda_k\eta}\, v_k. \tag{11}
--   $$
--
--   The same eigenvectors and eigenvalues serve for every $\eta > -1$. Thus the optimal portfolios of all ambiguity-averse investors who share $\Sigma_R$ and $\Sigma_M$ are linear combinations of a fixed set of basis portfolios (eigenvectors of $Q$), whatever their coefficient of relative ambiguity aversion; only the weights $1/(1+\lambda_k\eta)$ change with $\eta$.
--
--   **Formalization Note** Assets are indexed by `Fin N`; $\mathcal S^N_{++}$ is `Matrix.PosDef`, $0\le\Sigma_M$ is `PosSemidef`, and $\Sigma_M \le \Sigma_R$ is positive semidefiniteness of $\Sigma_R - \Sigma_M$. An eigenvector is a nonzero $v$ with $Qv = \lambda v$ for a real $\lambda$; distinctness of the eigenvalues is injectivity of $k \mapsto \lambda_k$. The inverses are Mathlib's total matrix inverses; no invertibility hypothesis is added, because $I+\eta Q$ is invertible for $\eta>-1$ under the stated assumptions.
--
--   Differences from the source:
--   - reading: the §3 setup prints "$\Sigma_X \in \mathcal S^N_{++}$ and $0 \le \Sigma_M \le \Sigma_X$" → Lean assumes $\Sigma_R$ positive definite and $0 \le \Sigma_M \le \Sigma_R$; reason: $\Sigma_X$ is never defined, $Q$ and $\zeta$ are defined with $\Sigma_R$ on the next lines, and §2.2 (p.10) states $\Sigma_R \in \mathcal S^N_{++}$ and $0 \le \Sigma_M \le \Sigma_R$.
--   - encoding: $\zeta : (-1,\infty)\to\mathbb R^N$ → a total function of $\eta \in \mathbb R$ with the conclusion quantified over $\eta > -1$; reason: Lean convention, the same instances.
--   - encoding: "a positive integer $K$ and eigenvectors $v_1,\dots,v_K$ with distinct eigenvalues" → `K : ℕ` with `0 < K`, `v : Fin K → Fin N → ℝ` nonzero with `Q *ᵥ v k = λ k • v k`, `λ` injective; reason: Lean convention, the same instances.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), Theorem 1, pp.14–15 (setup §3, p.14; eq. (10), (11))

import Mathlib
import Definitions.Def_ImpliedAmbiguity_excessReturn
import Definitions.Def_ImpliedAmbiguity_Supplement_Q
import Definitions.Def_ImpliedAmbiguity_Supplement_zeta

open Matrix

namespace ImpliedAmbiguity.Supplement

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
Theorem 1 (Optimal portfolio in terms of basis portfolios), pp.14–15, in the setting of §3, p.14
(`Σ_R ∈ S^N_++`, `0 ≤ Σ_M ≤ Σ_R`, `Q = Σ_R⁻¹Σ_M`, `ζ` as in (10)): if `µ − R_f 1 ≠ 0`, there are a
positive integer `K` and eigenvectors `v_1, …, v_K` of `Q` with distinct eigenvalues
`λ_1, …, λ_K` such that, for every `η > −1`, (11) `ζ(η) = ∑_{k=1}^K (1/(1 + λ_k η)) v_k`.

**Formalization Note.** The §3 setup prints "`Σ_X ∈ S^N_++` and `0 ≤ Σ_M ≤ Σ_X`"; `Σ_X` is a
misprint for `Σ_R` (Q and ζ are defined with `Σ_R` on the next lines, and §2.2, p.10 assumes
`Σ_R ∈ S^N_++`, `0 ≤ Σ_M ≤ Σ_R`). `S^N_++` is `Matrix.PosDef`, `0 ≤ Σ_M` is
`SigmaM.PosSemidef` and `Σ_M ≤ Σ_R` is `(SigmaR - SigmaM).PosSemidef` (p.10). An eigenvector of
`Q` with eigenvalue `λ ∈ ℝ` is a nonzero `v` with `Q *ᵥ v = λ • v`; "distinct" is injectivity of
`λ : Fin K → ℝ`. The eigen-decomposition is chosen once, for all `η > −1` simultaneously. -/
theorem theorem_1 {N : ℕ} (SigmaR SigmaM : Matrix (Fin N) (Fin N) ℝ) (hSigmaR : SigmaR.PosDef)
    (hSigmaM : SigmaM.PosSemidef) (hMR : (SigmaR - SigmaM).PosSemidef)
    (μ : Fin N → ℝ) (Rf : ℝ) (hc : excessReturn μ Rf ≠ 0) :
    ∃ K : ℕ, 0 < K ∧ ∃ (v : Fin K → Fin N → ℝ) (lam : Fin K → ℝ),
      Function.Injective lam ∧
      (∀ k, v k ≠ 0 ∧ Q SigmaR SigmaM *ᵥ v k = lam k • v k) ∧
      ∀ η : ℝ, -1 < η →
        zeta SigmaR SigmaM (excessReturn μ Rf) η = ∑ k, (1 / (1 + lam k * η)) • v k := by sorry

end ImpliedAmbiguity.Supplement

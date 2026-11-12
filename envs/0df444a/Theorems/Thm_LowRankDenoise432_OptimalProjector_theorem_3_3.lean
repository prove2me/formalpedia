-- Prove2me | Theorems.Thm_LowRankDenoise432_OptimalProjector_theorem_3_3
-- name    : LowRankDenoise432.OptimalProjector.theorem_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:42.133352+00:00
-- url     : https://prove2.me/theorems/4e762875-194c-4779-a1d2-09c41976e399
-- title:
--   Theorem 3.3 — exact error and optimal projector (all clauses)
-- statement:
--   Work in the model of Section 2: a random cost $c\in\mathbb R^d$ with mean $\bar c$ and covariance $\Sigma_c$; $m\ge1$ bounded noise replications that, given $c$, have mean zero, are uncorrelated across replications and coordinates, and have a common conditional variance; $D=\mathbb E[\operatorname{diag}(\operatorname{Var}(\varepsilon_e\mid c))]$; $\bar y_m=c+\bar\varepsilon$. For a deterministic orthogonal projector $\Pi$ let
--   $$\operatorname{err}(\Pi)=\mathbb E\,\|\hat c_\Pi-c\|^2,\qquad \hat c_\Pi=\bar c+\Pi(\bar y_m-\bar c).$$
--   Write $\lambda_1\ge\dots\ge\lambda_d$ for the eigenvalues of $\Sigma_c-D/m$ (with multiplicity) and $\Pi^+$ for the orthogonal projector onto its positive eigenspace. Then:
--   1. For every orthogonal projector $\Pi$ (equation (2)),
--   $$\operatorname{err}(\Pi)=\frac{\operatorname{tr}(\Pi D)}{m}+\operatorname{tr}\big((I-\Pi)\Sigma_c\big)=\operatorname{tr}\Sigma_c-\operatorname{tr}\Big(\Pi\big(\Sigma_c-\tfrac Dm\big)\Big).$$
--   2. $\Pi^+$ is an orthogonal projector and $\operatorname{err}(\Pi^+)\le\operatorname{err}(\Pi)$ for every orthogonal projector $\Pi$, of any rank.
--   3. $\operatorname{err}(\Pi^+)=\operatorname{tr}\Sigma_c-\sum_j(\lambda_j)_+$, and this is at most $\operatorname{tr}D/m$ and at most $\operatorname{tr}\Sigma_c$.
--   4. For every $k\le d$ and every orthonormal basis $u_1,\dots,u_d$ of eigenvectors of $\Sigma_c-D/m$ whose eigenvalues are non-increasing, $P_k=\sum_{j\le k}u_ju_j^\top$ is an orthogonal projector of rank $k$, and $\operatorname{err}(P_k)\le\operatorname{err}(\Pi)$ for every orthogonal projector $\Pi$ of rank $k$.
--   5. The optimal rank $k^*(m)=\#\{j:\lambda_j(\Sigma_c-D/m)>0\}$ equals $\operatorname{rank}\Pi^+$, and $k^*(m_1)\le k^*(m_2)$ whenever $1\le m_1\le m_2$, with $\Sigma_c$ and $D$ fixed.
--   6. If $D=\sigma^2I$ for a real $\sigma$, then $\Pi^+$ is the orthogonal projector onto the span of the eigenvectors of the observed covariance $\Sigma_c+\sigma^2I/m$ whose eigenvalue exceeds $2\sigma^2/m$.
--
--   The theorem gives the exact risk of every projection denoiser and the optimal one: retain a direction exactly when its signal variance exceeds the noise it lets through, a hard threshold at twice the noise variance on the observed spectrum.
--
--   **Formalization Note.** The error is a genuine Bochner integral; $\Sigma_c$ is Mathlib's `covariance`, $D$ is built from `condVar` given $\sigma(c)$, $\Pi^+$ is the orthogonal projection onto the span of eigenvectors with positive eigenvalue, and the eigenvalues are `eigenvalues₀`, sorted non-increasingly. "Projector" means a symmetric idempotent matrix.
--
--   Differences from the source:
--   - generalization: given c, the replications are independent with mean zero and independent coordinates → given σ(c), zero conditional mean and zero conditional cross moments for every pair (r,e) ≠ (s,f); reason: conditional independence with zero conditional mean implies these second-moment conditions, so every source model satisfies them; Mathlib's CondIndepFun would add [StandardBorelSpace Ω], which the source does not assume
--   - reading: Var(ε_e | c), written without a replication index → the conditional variance of ε⁽ʳ⁾_e given σ(c) is a.s. the same for every r, and D uses the first replication; reason: the source's notation presupposes one conditional variance per coordinate
--   - encoding: a random cost vector c with mean c̄ and covariance Σc → c measurable with every coordinate in L²; reason: the source's covariance presupposes finite second moments
--   - reading: among rank-k projectors the minimizer is the top-k eigenspace of Σc − D/m → every top-k eigenspace projector, built from any orthonormal eigenbasis with non-increasing eigenvalues, is a minimizer; reason: uniqueness is false (Σc = I, D = 0, d ≥ 2, k = 1: every rank-1 projector has error d − 1), and the existence reading covers every choice of top-k eigenspace
--   - encoding: the projector onto the positive eigenspace; the span of the eigenvectors → the matrix of the orthogonal projection onto the span of all eigenvectors with eigenvalue > 0 (resp. > 2σ²/m); reason: the canonical construction; no basis choice
--   - encoding: D = σ²I → noiseVar = σ² • 1 for a real σ; reason: the same matrices
--   - generalization: edge costs on a directed acyclic graph → arbitrary finite-dimensional real cost vectors without graph data; reason: the estimator error and every conclusion depend only on the cost and noise model, so every source graph instance is included
--   - encoding: coordinates and replications numbered from one, with Euclidean squared error → Fin d and Fin m indices from zero, sqNorm as the sum of squared coordinates, m > 0; reason: same finite-dimensional vectors, all dimensions and positive replication counts; d = 0 is harmless
--   - encoding: fixed projector Π with centre c̄′ = c̄ → a deterministic matrix Q with centre computed as the coordinatewise expectation; reason: fixed matrices are automatically independent of the test noise; no restriction on their rank is added
-- source:
--   Henry Aldridge-Krawciw, Irene Aldridge, Low-Rank Denoising for Predict-then-Optimize, STOC 2027 submission #432 (October 2026), source.pdf SHA-256 8d92579f841e1b4853ee9eecd477b739374858db635a23defcc3fb767b137889, PDF p.2, Theorem 3.3 (Exact error and optimal projector), eq. (2); model Section 2, PDF p.2; proof PDF p.6

import Mathlib
import Definitions.Def_LowRankDenoise432_OptimalProjector_Model
open MeasureTheory Matrix

namespace LowRankDenoise432.OptimalProjector

/-- Theorem 3.3 (Exact error and optimal projector), PDF p.2, all clauses. Here `Σ_c = M.costCov`,
`D = M.noiseVar`, `Σ_c − D/n = M.adjCov n`, `λ_j(Σ_c − D/n) = M.eigs n j` (non-increasing),
`k*(n) = M.optRank n`, and `err Q = 𝔼‖c̄ + Q(ȳ_m − c̄) − c‖²`.
1. (2): both expressions of the error, for every orthogonal projector `Q`;
2. `Π⁺ = posProj (Σ_c − D/m)` is an orthogonal projector minimizing the error over all of them;
3. its error is `tr Σ_c − ∑ⱼ (λⱼ)₊`, which is at most `tr D / m` and at most `tr Σ_c`;
4. for every `k ≤ d` and every orthonormal eigenbasis `u` of `Σ_c − D/m` with non-increasing
   eigenvalues, `∑_{j<k} u_j u_jᵀ` is a rank-`k` orthogonal projector minimizing the error over
   all rank-`k` orthogonal projectors;
5. `k*(m) = rank Π⁺`, and `k*` is non-decreasing in the replication count;
6. if `D = σ² I`, then `Π⁺` is the orthogonal projector onto the span of the eigenvectors of
   `Σ_c + σ² I / m` with eigenvalue greater than `2σ²/m`. -/
theorem theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) :
    -- (1) equation (2)
    (∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q →
      M.err Q = trace (Q * M.noiseVar) / m + trace ((1 - Q) * M.costCov) ∧
      M.err Q = trace M.costCov - trace (Q * M.adjCov m)) ∧
    -- (2) global optimality of the positive-eigenspace projector
    (IsOrthProjector (posProj (M.adjCov m)) ∧
      ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q →
        M.err (posProj (M.adjCov m)) ≤ M.err Q) ∧
    -- (3) the minimum value and its two upper bounds
    (M.err (posProj (M.adjCov m)) = trace M.costCov - ∑ j, max (M.eigs m j) 0 ∧
      M.err (posProj (M.adjCov m)) ≤ trace M.noiseVar / m ∧
      M.err (posProj (M.adjCov m)) ≤ trace M.costCov) ∧
    -- (4) rank-k optimality of every top-k eigenspace projector
    (∀ k : ℕ, k ≤ d → ∀ (u : Fin d → Fin d → ℝ) (μ : Fin d → ℝ),
      (∀ i j, u i ⬝ᵥ u j = if i = j then 1 else 0) →
      (∀ j, M.adjCov m *ᵥ u j = μ j • u j) → Antitone μ →
      IsOrthProjector (topProj u k) ∧ (topProj u k).rank = k ∧
        ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q → Q.rank = k →
          M.err (topProj u k) ≤ M.err Q) ∧
    -- (5) the optimal rank k*(m)
    (M.optRank m = (posProj (M.adjCov m)).rank ∧
      ∀ m₁ m₂ : ℕ, 0 < m₁ → m₁ ≤ m₂ → M.optRank m₁ ≤ M.optRank m₂) ∧
    -- (6) the homoscedastic case D = σ² I
    (∀ σ : ℝ, M.noiseVar = σ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
      posProj (M.adjCov m) =
        orthProjMatrix (eigSpanAbove (M.costCov + (σ ^ 2 / m) • (1 : Matrix (Fin d) (Fin d) ℝ))
          (2 * σ ^ 2 / m))) := by sorry

end LowRankDenoise432.OptimalProjector

-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_exists_whitening_tendsto_moments_readable
-- name    : FunctionalInequalities.KLS.exists_whitening_tendsto_moments_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:15.412333+00:00
-- url     : https://prove2.me/theorems/e2bcc388-90fd-4d11-8bef-4995ad9590a2
-- title:
--   Whitening Preserves Low-Moment Convergence
-- statement:
--   This statement constructs affine whitening maps that preserve convergence of moments through degree four.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $(λ_k)$ and $μ$ be probability measures on $E$, and assume `Isotropic μ`. Fix $R\in\mathbb R$. Suppose:
--
--   1. every $λ_k$ and $μ$ give measure zero to the complement of the closed ball $\overline B(0,R)$;
--   2. for every $d\le4$ and every $v:\operatorname{Fin}(d)\to E$, the mixed moments of $λ_k$ converge to those of $μ$.
--
--   Then there exist continuous linear equivalences $L_k:E\simeq_L E$ and centers $c_k\in E$ such that, for all sufficiently large $k$,
--
--   $$
--   \int L_k(x-c_k)\,dλ_k(x)=0,
--   $$
--
--   and, for every $u,v\in E$,
--
--   $$
--   \int \langle u,L_k(x-c_k)\rangle\langle v,L_k(x-c_k)\rangle\,dλ_k(x)=\langle u,v\rangle.
--   $$
--
--   Moreover, the mixed moments of the transformed laws through degree four converge to the corresponding moments of $μ$. This is the affine whitening step in the regular approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_whitening_tendsto_moments [MeasurableSpace E] [BorelSpace E] {lam : ℕ → ProbabilityMeasure E}
--       {μ : ProbabilityMeasure E} (hiso : Isotropic μ) {R : ℝ}
--       (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
--       (hμsupp : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0)
--       (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
--         Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
--           (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
--       ∃ (L : ℕ → E ≃L[ℝ] E) (c : ℕ → E),
--         (∀ᶠ k in atTop, ∫ x, L k (x - c k) ∂(lam k : Measure E) = 0 ∧
--           ∀ u v : E, ∫ x, ⟪u, L k (x - c k)⟫ * ⟪v, L k (x - c k)⟫ ∂(lam k : Measure E) = ⟪u, v⟫) ∧
--         ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
--           Tendsto (fun k => ∫ x, ∏ i, ⟪v i, L k (x - c k)⟫ ∂(lam k : Measure E)) atTop
--             (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/BallConditioning`](https://prove2.me/theorems/2fa3d0ff-8849-4ff0-b13d-3697177849fc).
--
--   Definition modules: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Supporting theorems: [`covariance_tendsto_one`](https://prove2.me/theorems/931a2bcc-f8c0-48ee-8d9a-a38753c18c36), [`whitening_sequence`](https://prove2.me/theorems/4f39d579-4312-46d4-8a78-c4f9ba76eab9).
--
--   Previous: [`whitening_sequence`](https://prove2.me/theorems/4f39d579-4312-46d4-8a78-c4f9ba76eab9).
--
--   [Source excerpt, lines 461–473](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L461-L473) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L457-L524 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.BallConditioning`, declaration `FunctionalInequalities.KLS.exists_whitening_tendsto_moments`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning

open MeasureTheory Set Metric Filter
open scoped Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.KLS.exists_whitening_tendsto_moments_readable [MeasurableSpace E] [BorelSpace E] {lam : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hμsupp : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    ∃ (L : ℕ → E ≃L[ℝ] E) (c : ℕ → E),
      (∀ᶠ k in atTop, ∫ x, L k (x - c k) ∂(lam k : Measure E) = 0 ∧
        ∀ u v : E, ∫ x, ⟪u, L k (x - c k)⟫ * ⟪v, L k (x - c k)⟫ ∂(lam k : Measure E) = ⟪u, v⟫) ∧
      ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
        Tendsto (fun k => ∫ x, ∏ i, ⟪v i, L k (x - c k)⟫ ∂(lam k : Measure E)) atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by sorry

-- Prove2me | Theorems.Thm_HighDimStat_MetricEntropy_gaussian_comparison
-- name    : HighDimStat.MetricEntropy.gaussian_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:02:07.884978+00:00
-- url     : https://prove2.me/theorems/ba22b5c2-0f07-47ed-bc6f-38f7c14481d3
-- title:
--   Theorem 5.25 -- the Gaussian comparison principle
-- statement:
--   **Theorem 5.25 (Gaussian comparison).** Let $(X_1,\dots,X_N)$ and $(Y_1,\dots,Y_N)$ be a pair
--   of centered Gaussian random vectors, and suppose there exist disjoint subsets $A$ and $B$ of
--   $[N]\times[N]$ such that $\mathbb E[X_iX_j]\le\mathbb E[Y_iY_j]$ for all $(i,j)\in A$,
--   $\mathbb E[X_iX_j]\ge\mathbb E[Y_iY_j]$ for all $(i,j)\in B$, and
--   $\mathbb E[X_iX_j]=\mathbb E[Y_iY_j]$ for all $(i,j)\notin A\cup B$. Let $F:\mathbb R^N\to
--   \mathbb R$ be twice differentiable, with
--   $\partial^2F/\partial u_i\partial u_j(u)\ge 0$ for $(i,j)\in A$ and $\le 0$ for $(i,j)\in B$.
--   Then
--
--   $$
--   \mathbb E[F(X)] \;\le\; \mathbb E[F(Y)].
--   $$
--
--   This is the chapter's central Gaussian comparison principle (Section 5.4), the source of both
--   Slepian's inequality and the Sudakov–Fernique comparison as corollaries, obtained by
--   specializing $A$, $B$, and $F$.
--
--   **Formalization Note** "Centered Gaussian random vector" is realized as a random vector
--   `X : Ω → Fin N → ℝ` with `HasGaussianLaw X Prob` (Mathlib's predicate that the pushforward law
--   is a genuine multivariate Gaussian measure) together with the explicit coordinatewise
--   mean-zero condition; the covariances $\mathbb E[X_iX_j]$ are the literal Bochner integrals
--   $\int X_iX_j\,d\mathrm{Prob}$, guarded by explicit integrability hypotheses (trap 2). The mixed
--   second partial derivative $\partial^2F/\partial u_i\partial u_j(u)$ is realized as the iterated
--   Fréchet derivative `iteratedFDeriv ℝ 2 F u` applied to the two standard basis vectors
--   `Pi.single i 1`, `Pi.single j 1` — the sign-pattern hypothesis on mixed partials is kept
--   exactly as stated (some pairs $\ge 0$, others $\le 0$, over the disjoint sets $A$, $B$), not
--   simplified to a global convexity condition on $F$.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 144 (PDF p. 164), Theorem 5.25, Eqs. (5.52)-(5.54)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimStat.MetricEntropy

/-- **Theorem 5.25** (Gaussian comparison principle), Wainwright, *High-Dimensional Statistics*
(2019), p. 144. Let `X, Y : Ω → Fin N → ℝ` be a pair of centered Gaussian random vectors (each
with law `HasGaussianLaw` and coordinatewise mean zero), and suppose there exist disjoint subsets
`A` and `B` of `Fin N × Fin N` such that `E[XᵢXⱼ] ≤ E[YᵢYⱼ]` for `(i,j) ∈ A`, `E[XᵢXⱼ] ≥ E[YᵢYⱼ]`
for `(i,j) ∈ B`, and `E[XᵢXⱼ] = E[YᵢYⱼ]` for `(i,j) ∉ A ∪ B`. Let `F : (Fin N → ℝ) → ℝ` be twice differentiable (not necessarily with a
*continuous* second derivative: `F` itself differentiable everywhere, and its derivative map
`fderiv ℝ F` itself differentiable everywhere), with mixed second partial
`∂²F/∂uᵢ∂uⱼ(u) ≥ 0` for `(i,j) ∈ A` and `≤ 0` for `(i,j) ∈ B` (realized as the iterated Fréchet
derivative applied to the two standard basis vectors). Then `E[F(X)] ≤ E[F(Y)]`. -/
theorem gaussian_comparison {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] {N : ℕ} (X Y : Ω → Fin N → ℝ)
    (hXGauss : HasGaussianLaw X Prob) (hYGauss : HasGaussianLaw Y Prob)
    (hXmean : ∀ i, ∫ ω, X ω i ∂Prob = 0) (hYmean : ∀ i, ∫ ω, Y ω i ∂Prob = 0)
    (hXint : ∀ i j, Integrable (fun ω => X ω i * X ω j) Prob)
    (hYint : ∀ i j, Integrable (fun ω => Y ω i * Y ω j) Prob)
    (A B : Finset (Fin N × Fin N)) (hAB : Disjoint A B)
    (hCovA : ∀ p ∈ A, ∫ ω, X ω p.1 * X ω p.2 ∂Prob ≤ ∫ ω, Y ω p.1 * Y ω p.2 ∂Prob)
    (hCovB : ∀ p ∈ B, ∫ ω, Y ω p.1 * Y ω p.2 ∂Prob ≤ ∫ ω, X ω p.1 * X ω p.2 ∂Prob)
    (hCovEq : ∀ p : Fin N × Fin N, p ∉ A ∪ B →
      ∫ ω, X ω p.1 * X ω p.2 ∂Prob = ∫ ω, Y ω p.1 * Y ω p.2 ∂Prob)
    (F : (Fin N → ℝ) → ℝ) (hF1 : Differentiable ℝ F) (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hFA : ∀ p ∈ A, ∀ u, 0 ≤ iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1])
    (hFB : ∀ p ∈ B, ∀ u, iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1] ≤ 0)
    (hFXint : Integrable (fun ω => F (X ω)) Prob) (hFYint : Integrable (fun ω => F (Y ω)) Prob) :
    ∫ ω, F (X ω) ∂Prob ≤ ∫ ω, F (Y ω) ∂Prob := by sorry

end HighDimStat.MetricEntropy

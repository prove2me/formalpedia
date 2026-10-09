-- Prove2me | Theorems.Thm_NestedSA_NASA_theorem_2_b
-- name    : NestedSA.NASA.theorem_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:40:09.389982+00:00
-- url     : https://prove2.me/theorems/7aef3333-fbd9-414d-98a8-49b5112761ed
-- title:
--   Theorem 2(b) — bound on E[V(x^R, z^R)] for the τ-weighted random output index R
-- statement:
--   Under the hypotheses of Theorem 2(a), let $N\ge2$ and let $R\in\{1,\dots,N-1\}$ be drawn independently of the run with $P[R=k]=\tau_k/\sum_{j=1}^{N-1}\tau_j$ (3.34), so that
--   $$\mathbb E\big[V(x^R,z^R)\big]=\frac{\sum_{k=1}^{N-1}\tau_k\,\mathbb E[V(x^k,z^k)]}{\sum_{k=1}^{N-1}\tau_k}.$$
--   Then every $V(x^k,z^k)$ is integrable and
--   $$\mathbb E\big[V(x^R,z^R)\big]\le\frac1{\sum_{k=1}^{N-1}\tau_k}\Big\{\Big(\frac1c\big[a\bar c\max(L_1,L_2)+\max(1,\beta^2)\big]\hat\sigma^2+2a^2\bar c\,\sigma_J^2\sigma_s^2\Big)\sum_{k=0}^{N-1}\tau_k^2+\frac1c\big(a\bar c\max(L_1,L_2)+\max(1,\beta^2)\big)W(x^0,z^0,u^0)\Big\}.$$
--
--   This is the general complexity bound of NASA for an arbitrary admissible stepsize sequence; part (c) specializes it.
--
--   **Formalization Note** The expectation over the independent index $R$ is written as the $\tau$-weighted average above, the identity used on p. 16. The paper prints the first coefficient as $a\bar c\big(\frac1c[\max(L_1,L_2)+\max(1,\beta^2)]\sigma^2+2a\sigma_J^2\sigma_s^2\big)$; its proof (Lemma 4 for the $\|d^k\|^2$ part, which carries no factor $a\bar c$) establishes the coefficient stated here, which coincides with the printed one when $a\bar c=1$ (in particular in part (c)). $\hat\sigma^2$ replaces the printed $\sigma^2$ (see Proposition 1(b)).
-- source:
--   Ghadimi, Ruszczyński, Wang, A Single Time-Scale Stochastic Approximation Method for Nested Stochastic Optimization, arXiv:1812.01094v2, p. 14, Theorem 2(b), (3.33)–(3.34)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic
import Definitions.Def_NestedSA_NASA_Model

open MeasureTheory ProbabilityTheory

namespace NestedSA.NASA

/-- Theorem 2(b), (3.33)–(3.34) (p. 14), with the corrected constant `σ̂²` and the corrected coefficient of
`max(1, β²) σ̂²`. Under the hypotheses of Theorem 2(a), for every `N ≥ 2`, with `R` drawn independently with
`P[R = k] = τ_k / Σ_{j=1}^{N−1} τ_j` on `{1, …, N−1}`, so that
`E[V(x^R, z^R)] = Σ_{k=1}^{N−1} τ_k E[V(x^k, z^k)] / Σ_{k=1}^{N−1} τ_k`:
`E[V(x^R, z^R)] ≤ (1/Σ_{k=1}^{N−1} τ_k) {((1/c)(ac̄ max(L₁, L₂) + max(1, β²)) σ̂² + 2a²c̄σ_J²σ_s²) Σ_{k=0}^{N−1} τ_k²
  + (1/c)(ac̄ max(L₁, L₂) + max(1, β²)) W(x⁰, z⁰, u⁰)}`, with every `V(x^k, z^k)` integrable.
The paper prints `ac̄((1/c)[max(L₁, L₂) + max(1, β²)]σ² + 2aσ_J²σ_s²)`; the two agree when `ac̄ = 1`. -/
theorem theorem_2_b {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (hF_bdd : BddBelow ((fun x => f (g x)) '' X))
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsStochRun X P a b β τ x0 z0 u0 x z u G s J)
    (σG σJ σs : ℝ) (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) (hcβ : c ≤ a * β) (hcγ : 2 * c ≤ γ * b)
    (h316 : Lg ^ 2 * (a * Ldf + γ) ^ 2 ≤ 2 * (a * β - c) * (γ * b - 2 * c))
    (hτ_one : ∀ k, τ k ≤ 1) (hbτ : ∀ k, b * τ k ≤ 1) (hτ0 : τ 0 = 1 / a)
    (cbar : ℝ) (hcbar : 0 < cbar)
    (h330 : ∀ k N : ℕ, 1 ≤ N →
      ∑ i ∈ Finset.Icc (k + 1) N, τ i * Gamma a τ i ≤ cbar * Gamma a τ (k + 1))
    (haτ : ∀ k, 1 ≤ k → a * τ k ≤ 1 / Real.sqrt 2) :
    ∀ N : ℕ, 2 ≤ N →
      (∀ k, Integrable (fun ω => V P f g (x k ω) (z k ω)) μ) ∧
      (∑ k ∈ Finset.Icc 1 (N - 1), τ k * ∫ ω, V P f g (x k ω) (z k ω) ∂μ) /
          (∑ k ∈ Finset.Icc 1 (N - 1), τ k) ≤
        1 / (∑ k ∈ Finset.Icc 1 (N - 1), τ k) *
          ((1 / c * (a * cbar * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) + max 1 (β ^ 2)) *
                sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0
              + 2 * a ^ 2 * cbar * σJ ^ 2 * σs ^ 2) * (∑ k ∈ Finset.range N, τ k ^ 2)
            + 1 / c * (a * cbar * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) + max 1 (β ^ 2)) *
                W P f g X a γ β x0 z0 u0) := by sorry

end NestedSA.NASA

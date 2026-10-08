-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_4_1
-- name    : LogGammaPolymer.Variance.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:36.316978+00:00
-- url     : https://prove2.me/theorems/8dafdcc0-f2b4-4426-a8d6-ff22ce71f782
-- title:
--   Lemma 4.1 — Var^λ[log Z_{m,n}] ≤ Var^θ[log Z_{m,n}] + C(m + n)(θ − λ), uniformly on compacts
-- statement:
--   Write $\mathrm{Var}^\lambda$ for the variance computed under assumption (2.4) with $\lambda$ in place of $\theta$. Consider $0<\delta_0<\theta<\mu$. There is a constant $C<\infty$ such that for all $\lambda\in[\delta_0,\theta]$ and all $m,n$,
--   $$\mathrm{Var}^\lambda\bigl[\log Z_{m,n}\bigr]\le\mathrm{Var}^\theta\bigl[\log Z_{m,n}\bigr]+C(m+n)(\theta-\lambda)\qquad(4.1).$$
--   A single constant $C$ works for all $\delta_0<\theta<\mu$ that vary in a compact set.
--
--   Lowering the horizontal boundary parameter costs at most a linear amount of variance. In the upper-bound argument this comparison is applied with $\theta-\lambda$ of order $u/N$.
--
--   **Formalization Note** Stated in the compact-uniform form, which contains the pointwise form (take a one-point compact set): for every compact set $K$ of triples $(\delta_0,\theta,\mu)$ with $0<\delta_0<\theta<\mu$ there is one $C$. The two variances are computed in two environments on possibly different probability spaces (universe `Type`), one satisfying (2.4) with $\lambda$ and one with $\theta$; the variance depends only on the law. The conclusion also asserts that $\log Z_{m,n}$ is square integrable under the $\lambda$-environment.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 4.1, (4.1), p. 19

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_4_1 (K : Set (ℝ × ℝ × ℝ)) (hK : IsCompact K)
    (hKpar : ∀ p ∈ K, 0 < p.1 ∧ p.1 < p.2.1 ∧ p.2.1 < p.2.2) :
    ∃ C : ℝ, ∀ δ₀ θ μ : ℝ, (δ₀, θ, μ) ∈ K → ∀ lam ∈ Set.Icc δ₀ θ, ∀ m n : ℕ,
      ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
        (E₁ : Env lam μ P₁)
        {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (E₂ : Env θ μ P₂),
      MemLp (logZ E₁ m n) 2 P₁ ∧
      variance (logZ E₁ m n) P₁ ≤
        variance (logZ E₂ m n) P₂ + C * ((m : ℝ) + n) * (θ - lam) := by sorry

end LogGammaPolymer.Variance

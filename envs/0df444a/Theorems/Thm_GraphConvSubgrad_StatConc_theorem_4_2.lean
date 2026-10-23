-- Prove2me | Theorems.Thm_GraphConvSubgrad_StatConc_theorem_4_2
-- name    : GraphConvSubgrad.StatConc.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:27.576187+00:00
-- url     : https://prove2.me/theorems/2c8eaefe-b916-4987-bdb3-bbedf6371612
-- title:
--   Theorem 4.2, (4.7), p. 13 — McDiarmid extended: ψ_{g−Eg}(λ) ≤ Σᵢ ψ_{εᵢωᵢ}(λ) for data-dependent bounded differences
-- statement:
--   Let $z=(z_1,\dots,z_m)$ have independent coordinates, $z_i\sim\mu_i$ on a space $\mathcal Z_i$. Let $g$ be a measurable, integrable function of $z$, and let $\omega_i:\mathcal Z_i\times\mathcal Z_i\to\mathbb R_+$ be measurable functions such that changing the $i$-th coordinate changes $g$ by at most $\omega_i$:
--   $$|g(z_1,\dots,z_i,\dots,z_m)-g(z_1,\dots,z_i',\dots,z_m)|\le\omega_i(z_i,z_i')\qquad\text{for all }z,\ i,\ z_i'.$$
--   For $\lambda\in\mathbb R$ write $\psi_{\varepsilon_i\omega_i}(\lambda)=\log\mathbb E\,e^{\lambda\varepsilon_i\omega_i(z_i,z_i')}=\log\mathbb E\cosh(\lambda\,\omega_i(z_i,z_i'))$, where $z_i'$ is an independent copy of $z_i$ and $\varepsilon_i$ a Rademacher sign. Then for every $\lambda$ at which each $\cosh(\lambda\omega_i)$ is integrable, $e^{\lambda(g(z)-\mathbb E g(z))}$ is integrable and
--   $$\psi_{g(z)-\mathbb E[g(z)]}(\lambda)=\log\mathbb E\,e^{\lambda(g(z)-\mathbb E g(z))}\le\sum_{i=1}^m\psi_{\varepsilon_i\omega_i}(\lambda).\tag{4.7}$$
--
--   This extends McDiarmid's bounded-differences inequality from constant differences $c_i$ to differences that depend on the data, so that an unbounded but light-tailed Lipschitz constant $L$ can be used in Theorem 4.4.
--
--   **Formalization Note** The left side is Mathlib's cumulant generating function `cgf` of $g-\mathbb E g$ under the product measure. At $\lambda$ where some $\cosh(\lambda\omega_i)$ is not integrable the paper's right side is $+\infty$ and there is nothing to prove; those $\lambda$ are excluded. Measurability and integrability of $g$ and measurability of $\omega_i$ are added; the page's "random variables" presuppose them.
-- source:
--   Davis, Drusvyatskiy, Graphical Convergence of Subgradients in Nonconvex Optimization and Learning, arXiv:1810.07590v2, p. 13, Theorem 4.2, (4.7)

import Mathlib
import Definitions.Def_GraphConvSubgrad_StatConc_Setting

namespace GraphConvSubgrad.StatConc

open MeasureTheory ProbabilityTheory

/-- Theorem 4.2 (McDiarmid extended), (4.7), p. 13. Let `z = (z₁, …, z_m)` have independent
coordinates `zᵢ ∼ μᵢ` on `Zᵢ`, and let `g` change by at most `ωᵢ(zᵢ, z'ᵢ) ≥ 0` when the `i`-th
coordinate is replaced by `z'ᵢ`. Then for every `λ` at which every `cosh(λ ωᵢ)` is integrable
under `μᵢ ⊗ μᵢ`, `e^{λ(g − E g)}` is integrable and
`ψ_{g(z) − E g(z)}(λ) ≤ ∑ᵢ ψ_{εᵢ ωᵢ}(λ)`, where `ψ_{εᵢωᵢ}(λ) = log E cosh(λ ωᵢ(zᵢ, z'ᵢ))` with `z'ᵢ`
an independent copy of `zᵢ`. Added: `g` measurable and integrable, `ωᵢ` measurable. -/
theorem theorem_4_2 {m : ℕ} {Z : Fin m → Type*} [∀ i, MeasurableSpace (Z i)]
    (μ : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (μ i)]
    (g : (∀ i, Z i) → ℝ) (hg_meas : Measurable g) (hg_int : Integrable g (Measure.pi μ))
    (ω : ∀ i, Z i → Z i → ℝ) (hω_nonneg : ∀ i u v, 0 ≤ ω i u v)
    (hω_meas : ∀ i, Measurable (Function.uncurry (ω i)))
    (hbd : ∀ (z : ∀ i, Z i) (i : Fin m) (z'i : Z i),
      |g z - g (Function.update z i z'i)| ≤ ω i (z i) z'i)
    (lam : ℝ)
    (hlam : ∀ i, Integrable (fun p : Z i × Z i => Real.cosh (lam * ω i p.1 p.2))
      ((μ i).prod (μ i))) :
    Integrable (fun z => Real.exp (lam * (g z - ∫ w, g w ∂(Measure.pi μ)))) (Measure.pi μ) ∧
      cgf (fun z => g z - ∫ w, g w ∂(Measure.pi μ)) (Measure.pi μ) lam
        ≤ ∑ i, logMGFSym ((μ i).prod (μ i)) (Function.uncurry (ω i)) lam := by sorry

end GraphConvSubgrad.StatConc

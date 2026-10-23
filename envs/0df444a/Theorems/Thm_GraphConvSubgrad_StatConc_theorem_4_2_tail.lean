-- Prove2me | Theorems.Thm_GraphConvSubgrad_StatConc_theorem_4_2_tail
-- name    : GraphConvSubgrad.StatConc.theorem_4_2_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:23.106126+00:00
-- url     : https://prove2.me/theorems/4b3af5fa-f5b1-4e56-bc62-1a6d95b655ef
-- title:
--   Theorem 4.2, (4.8), p. 14 — McDiarmid extended, tail bound P(g − Eg ≥ t) ≤ exp(−mψ⋆_{εω}(t/m)), i.i.d. case
-- statement:
--   Let $z_1,\dots,z_m$ ($m\ge1$) be independent with a common law $\mu$ on $\Omega$. Let $g$ be a measurable, integrable function of $z=(z_1,\dots,z_m)$, and let $\omega:\Omega\times\Omega\to\mathbb R_+$ be measurable with
--   $$|g(z_1,\dots,z_i,\dots,z_m)-g(z_1,\dots,z_i',\dots,z_m)|\le\omega(z_i,z_i')\qquad\text{for all }z,\ i,\ z_i'.$$
--   Write $\psi_{\varepsilon\omega}(\lambda)=\log\mathbb E\cosh(\lambda\,\omega(z,z'))$ with $z,z'$ independent of law $\mu$, and $\psi^\star_{\varepsilon\omega}(t)=\sup_\lambda\{t\lambda-\psi_{\varepsilon\omega}(\lambda)\}$. Then for every $t\ge0$,
--   $$\mathbb P\big(g(z)-\mathbb E[g(z)]\ge t\big)\le\exp\Big(-m\,\psi^\star_{\varepsilon\omega}\Big(\frac tm\Big)\Big).\tag{4.8}$$
--   Equivalently, for every $\lambda$ with $\cosh(\lambda\omega)$ integrable,
--   $$\mathbb P\big(g(z)-\mathbb E[g(z)]\ge t\big)\le\exp\Big(-m\Big(\lambda\frac tm-\psi_{\varepsilon\omega}(\lambda)\Big)\Big),$$
--   which is how the statement is formalized.
--
--   This is the tail form of the extended McDiarmid inequality that the proof of Theorem 4.4 applies, for a fixed centre, to the distance between the empirical and the population proximal points.
--
--   **Formalization Note** The page says "if $\omega_i=\omega_j$ for all $i,j$". The $m$ terms $\psi_{\varepsilon_i\omega_i}$ of (4.7) coincide only if the laws of the $z_i$ coincide as well, so the statement assumes i.i.d. coordinates, which is the case used in Theorem 4.4. The conjugate $\psi^\star$ may be $+\infty$, so the bound is stated for every admissible $\lambda$ (a $\lambda$ with $\cosh(\lambda\omega)$ not integrable has $\psi=+\infty$ and contributes nothing to the supremum). Added: $m\ge1$, measurability and integrability of $g$, measurability of $\omega$.
-- source:
--   Davis, Drusvyatskiy, Graphical Convergence of Subgradients in Nonconvex Optimization and Learning, arXiv:1810.07590v2, pp. 13–14, Theorem 4.2, (4.8)

import Mathlib
import Definitions.Def_GraphConvSubgrad_StatConc_Setting

namespace GraphConvSubgrad.StatConc

open MeasureTheory

/-- Theorem 4.2 (McDiarmid extended), (4.8), p. 14, in the identically distributed case. Let
`z₁, …, z_m` be i.i.d. with law `μ` and let `g` change by at most `ω(zᵢ, z'ᵢ) ≥ 0` when any one
coordinate `zᵢ` is replaced by `z'ᵢ`. Then for every `t ≥ 0`,
`P(g(z) − E g(z) ≥ t) ≤ exp(−m ψ⋆_{εω}(t/m))`, written as: for every `λ` with `cosh(λ ω)`
integrable under `μ ⊗ μ`, `P(g − E g ≥ t) ≤ exp(−m (λ t/m − ψ_{εω}(λ)))`. Added: `0 < m`, a common
law, `g` measurable and integrable, `ω` measurable. -/
theorem theorem_4_2_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (g : (Fin m → Ω) → ℝ) (hg_meas : Measurable g)
    (hg_int : Integrable g (Measure.pi fun _ : Fin m => μ))
    (ω : Ω → Ω → ℝ) (hω_nonneg : ∀ u v, 0 ≤ ω u v) (hω_meas : Measurable (Function.uncurry ω))
    (hbd : ∀ (z : Fin m → Ω) (i : Fin m) (z'i : Ω),
      |g z - g (Function.update z i z'i)| ≤ ω (z i) z'i)
    (t : ℝ) (ht : 0 ≤ t) (lam : ℝ)
    (hlam : Integrable (fun p : Ω × Ω => Real.cosh (lam * ω p.1 p.2)) (μ.prod μ)) :
    (Measure.pi fun _ : Fin m => μ)
        {z | t ≤ g z - ∫ w, g w ∂(Measure.pi fun _ : Fin m => μ)}
      ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) *
          (lam * (t / m) - logMGFSym (μ.prod μ) (Function.uncurry ω) lam)))) := by sorry

end GraphConvSubgrad.StatConc

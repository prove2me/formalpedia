-- Prove2me | Theorems.Thm_FournierGuillin_Conc_lemma_13
-- name    : FournierGuillin.Conc.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:14.961788+00:00
-- url     : https://prove2.me/theorems/f50f696f-c754-4162-a60f-84f0be577e56
-- title:
--   Lemma 13, p. 14 — ℙ[Z^p_N ≥ x] ≤ C exp(−cNx²)1_{x≤x₀} + C·(term under (1), (2) or (3))
-- statement:
--   Let $d\ge1$, $p>0$, and fix $x_0>0$. Put $Z^p_N=\sum_{n\ge0}2^{pn}|\mu_N(B_n)-\mu(B_n)|$, with $B_n$ as in Notation 4(b). Then, for $\mu\in\mathcal P(\mathbb R^d)$ and all $N\ge1$, $x>0$,
--   $$\mathbb P[Z^p_N\ge x]\le C\exp(-cNx^2)\mathbf 1_{\{x\le x_0\}}+C\times\begin{cases}\exp(-cNx^{\alpha/p})\mathbf 1_{\{x>x_0\}} & \text{under (1)},\\ \exp(-c(Nx)^{(\alpha-\varepsilon)/p})\mathbf 1_{\{x\le x_0\}}+\exp(-c(Nx)^{\alpha/p})\mathbf 1_{\{x>x_0\}} & \forall\varepsilon\in(0,\alpha)\ \text{under (2)},\\ N(Nx)^{-(q-\varepsilon)/p} & \forall\varepsilon\in(0,q)\ \text{under (3)},\end{cases}$$
--   where the conditions are those of Theorem 2: (1) $\mathcal E_{\alpha,\gamma}(\mu)<\infty$ with $\alpha>p$, $\gamma>0$; (2) $\mathcal E_{\alpha,\gamma}(\mu)<\infty$ with $\alpha\in(0,p)$, $\gamma>0$; (3) $M_q(\mu)<\infty$ with $q>2p$. The constants $C,c>0$ depend on $p$, $d$, $x_0$ and on the parameters of the condition, including the value of the moment ($\mathcal E_{\alpha,\gamma}(\mu)$, resp. $M_q(\mu)$) and $\varepsilon$, but not otherwise on $\mu$, $N$ or $x$.
--
--   This handles the first of the two terms into which $\mathcal D_p(\mu_N,\mu)$ splits in the proof of Theorem 2: the fluctuation of the masses of the shells.
--
--   **Formalization Note** Each part is a separate statement with its own constants: its parameters, the moment value $E_0$ (resp. $M_0$), $\varepsilon$ and $x_0$ are quantified before $\exists\,C,c$, and $\mu$ (with $\mathcal E_{\alpha,\gamma}(\mu)=E_0$, resp. $M_q(\mu)=M_0$), $N$, $x$ after. "Let $x_0$ be fixed" is read as $x_0>0$; the proof of Theorem 2 uses $x_0=1/(2\kappa_{p,d})$. $Z^p_N$ is valued in $[0,\infty]$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Lemma 13, p. 14; proof pp. 14–18

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Lemma 13 (p. 14): for `μ ∈ P(ℝ^d)`, `p > 0` and a fixed `x₀ > 0`, under each of the conditions
(1), (2), (3) of Theorem 2 there are `C, c > 0` (depending on `p, d, x₀` and the parameters of the
condition, including the moment's value) such that for all `N ≥ 1` and `x > 0`,
`ℙ[Z^p_N ≥ x] ≤ C exp(-cNx²) 1_{x ≤ x₀} + C × (the condition's term)`. -/
theorem lemma_13 (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) (x₀ : ℝ) (hx₀ : 0 < x₀) :
    (∀ α γ : ℝ, p < α → 0 < γ → ∀ E₀ : ℝ≥0∞, E₀ < ⊤ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], expMoment α γ μ = E₀ →
          ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
            Measure.pi (fun _ : Fin N => μ) {ω | ENNReal.ofReal x ≤ Zp p μ ω} ≤
              ENNReal.ofReal (C * Real.exp (-(c * N * x ^ 2)) * (if x ≤ x₀ then 1 else 0) +
                C * Real.exp (-(c * N * x ^ (α / p))) * (if x₀ < x then 1 else 0))) ∧
    (∀ α γ : ℝ, 0 < α → α < p → 0 < γ → ∀ E₀ : ℝ≥0∞, E₀ < ⊤ → ∀ ε : ℝ, 0 < ε → ε < α →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], expMoment α γ μ = E₀ →
          ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
            Measure.pi (fun _ : Fin N => μ) {ω | ENNReal.ofReal x ≤ Zp p μ ω} ≤
              ENNReal.ofReal (C * Real.exp (-(c * N * x ^ 2)) * (if x ≤ x₀ then 1 else 0) +
                C * (Real.exp (-(c * (N * x) ^ ((α - ε) / p))) * (if x ≤ x₀ then 1 else 0) +
                  Real.exp (-(c * (N * x) ^ (α / p))) * (if x₀ < x then 1 else 0)))) ∧
    (∀ q : ℝ, 2 * p < q → ∀ M₀ : ℝ≥0∞, M₀ < ⊤ → ∀ ε : ℝ, 0 < ε → ε < q →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], FournierGuillin.Moment.moment q μ = M₀ →
          ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
            Measure.pi (fun _ : Fin N => μ) {ω | ENNReal.ofReal x ≤ Zp p μ ω} ≤
              ENNReal.ofReal (C * Real.exp (-(c * N * x ^ 2)) * (if x ≤ x₀ then 1 else 0) +
                C * (N * (N * x) ^ (-((q - ε) / p))))) := by sorry

end FournierGuillin.Conc

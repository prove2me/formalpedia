-- Prove2me | Theorems.Thm_Maldacena1999_near_horizon_AdS7S4_AdS4S7_AdS3S3
-- name    : Maldacena1999.near_horizon_AdS7S4_AdS4S7_AdS3S3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:12:28.430085+00:00
-- url     : https://prove2.me/theorems/db66ec96-f929-4257-98fc-c1aba471bdc5
-- title:
--   Near-horizon limits of M5-, M2- and D1–D5-branes are $\mathrm{AdS}_7\times S^4$, $\mathrm{AdS}_4\times S^7$, $\mathrm{AdS}_3\times S^3$
-- statement:
--   For $p\ge0$ and $R>0$ let $\mathrm{AdS}_{p+2}$ be the hyperboloid $-X_{-1}^2-X_0^2+X_1^2+\dots+X_{p+1}^2=-R^2$ in $\mathbb R^{2,p+1}$ and $\Phi_R(U,x)$ its Poincaré parametrization (A.2), $U>0$, $x\in\mathbb R^{1,p}$. For a tangent vector $(\delta U,\delta x)$, the induced metric is $\eta\big(D\Phi_R(U,x)[\delta U,\delta x]\big)$, where $\eta$ is the flat form of signature $(2,p+1)$. The round metric of the unit sphere $S^n\subset\mathbb R^{n+1}$ at $\omega$ is $\|\delta\omega\|^2$ for $\delta\omega\perp\omega$. The theorem asserts the following three limits, where $\delta r$ is the image of $\delta U$ under the change of radial variable of each case.
--
--   1. **M5-branes** (Section 3.1). For $N\ge1$, with $r=U^2l_p^3$, $\delta r=2Ul_p^3\delta U$, $R_{\rm AdS}=2(\pi N)^{1/3}$, $R_{\rm sph}=(\pi N)^{1/3}$ and $U'=2(\pi N)^{1/6}U$:
--   $$\lim_{l_p\to0^+}\frac{ds^2_{(3.1)}}{l_p^2}=\eta\big(D\Phi_{R_{\rm AdS}}(U',x)[2(\pi N)^{1/6}\delta U,\delta x]\big)+R_{\rm sph}^2\|\delta\omega\|^2,\qquad p=5,\ n=4.$$
--   2. **M2-branes** (Section 3.2). For $N\ge1$ and $K=2^5\pi^2N$, with $r=\sqrt{Ul_p^3}$, $\delta r=\frac{l_p^3}{2\sqrt{Ul_p^3}}\delta U$, $R_{\rm AdS}=K^{1/6}/2$, $R_{\rm sph}=K^{1/6}$ and $U'=U/(2K^{1/6})$:
--   $$\lim_{l_p\to0^+}\frac{ds^2_{(3.3)}}{l_p^2}=\eta\big(D\Phi_{R_{\rm AdS}}(U',x)[\delta U/(2K^{1/6}),\delta x]\big)+R_{\rm sph}^2\|\delta\omega\|^2,\qquad p=2,\ n=7.$$
--   3. **D1–D5 system** (Section 4). For $g,v>0$, $Q_1,Q_5\ge1$, $g_6=g/\sqrt v$, with $r=\alpha'U$, $\delta r=\alpha'\delta U$ and $R_{\rm AdS}=R_{\rm sph}=\big(g_6\sqrt{Q_1Q_5}\big)^{1/2}$:
--   $$\lim_{\alpha'\to0^+}\frac{ds^2_{(4.2)}}{\alpha'}=\eta\big(D\Phi_{R_{\rm AdS}}(U,x)[\delta U,\delta x]\big)+R_{\rm sph}^2\|\delta\omega\|^2,\qquad p=1,\ n=3.$$
--
--   In words: in the decoupling limits of the paper, the M5-brane geometry becomes $\mathrm{AdS}_7\times S^4$ with $R_{\rm sph}=R_{\rm AdS}/2=l_p(\pi N)^{1/3}$, the M2-brane geometry becomes $\mathrm{AdS}_4\times S^7$ with $R_{\rm sph}=2R_{\rm AdS}=l_p(2^5\pi^2N)^{1/6}$, and the D1–D5 geometry becomes $\mathrm{AdS}_3\times S^3$ with $R_{\rm sph}^2=R_{\rm AdS}^2=\alpha'g_6\sqrt{Q_1Q_5}$.
--
--   **Formalization Note** The Poincaré coordinate $U'$ on $\mathrm{AdS}$ is the paper's $U$ multiplied by a constant, so that the limit metric has exactly the form (A.3). `ambientForm`, `poincareEmbedding` and `minkowskiForm` come from the published file `Maldacena1999_Defs`. Only the six-dimensional part of the D1–D5 geometry is modelled.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://arxiv.org/abs/hep-th/9711200, pp. 1121-1125, Sections 3.1, 3.2, 4 and Appendix eqs. (A.1)-(A.3)

import Mathlib
import Definitions.Def_Maldacena1999_BraneDefs

open Filter Topology

namespace Maldacena1999

theorem near_horizon_AdS7S4_AdS4S7_AdS3S3 :
    -- M5-branes: `AdS₇ × S⁴` with `R_sph = R_AdS / 2 = l_p (π N)^{1/3}`
    (∀ (N : ℕ), 0 < N → ∀ (U : ℝ), 0 < U → ∀ (x : Fin 6 → ℝ)
      (ω : EuclideanSpace ℝ (Fin 5)), ‖ω‖ = 1 →
      ∀ (δU : ℝ) (δx : Fin 6 → ℝ) (δω : EuclideanSpace ℝ (Fin 5)), inner ℝ ω δω = 0 →
      Tendsto
        (fun lp : ℝ => m5Metric N lp (U ^ 2 * lp ^ 3) δx (2 * U * lp ^ 3 * δU) δω / lp ^ 2)
        (𝓝[>] 0)
        (𝓝 (ambientForm 5 (fderiv ℝ (poincareEmbedding 5 (2 * (Real.pi * N) ^ (1 / 3 : ℝ)))
              (2 * (Real.pi * N) ^ (1 / 6 : ℝ) * U, x)
              (2 * (Real.pi * N) ^ (1 / 6 : ℝ) * δU, δx)) +
          ‖(Real.pi * N) ^ (1 / 3 : ℝ) • δω‖ ^ 2))) ∧
    -- M2-branes: `AdS₄ × S⁷` with `R_sph = 2 R_AdS = l_p (2⁵ π² N)^{1/6}`
    (∀ (N : ℕ), 0 < N → ∀ (U : ℝ), 0 < U → ∀ (x : Fin 3 → ℝ)
      (ω : EuclideanSpace ℝ (Fin 8)), ‖ω‖ = 1 →
      ∀ (δU : ℝ) (δx : Fin 3 → ℝ) (δω : EuclideanSpace ℝ (Fin 8)), inner ℝ ω δω = 0 →
      Tendsto
        (fun lp : ℝ => m2Metric N lp (Real.sqrt (U * lp ^ 3)) δx
          (lp ^ 3 / (2 * Real.sqrt (U * lp ^ 3)) * δU) δω / lp ^ 2)
        (𝓝[>] 0)
        (𝓝 (ambientForm 2
              (fderiv ℝ (poincareEmbedding 2 ((2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ) / 2))
                (U / (2 * (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ)), x)
                (δU / (2 * (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ)), δx)) +
          ‖(2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ) • δω‖ ^ 2))) ∧
    -- D1–D5 system: `AdS₃ × S³` with `R_sph² = R_AdS² = α' g₆ √(Q₁ Q₅)`, `g₆ = g / √v`
    (∀ (g v : ℝ), 0 < g → 0 < v → ∀ (Q1 Q5 : ℕ), 0 < Q1 → 0 < Q5 →
      ∀ (U : ℝ), 0 < U → ∀ (x : Fin 2 → ℝ) (ω : EuclideanSpace ℝ (Fin 4)), ‖ω‖ = 1 →
      ∀ (δU : ℝ) (δx : Fin 2 → ℝ) (δω : EuclideanSpace ℝ (Fin 4)), inner ℝ ω δω = 0 →
      Tendsto
        (fun α' : ℝ => d1d5Metric g v Q1 Q5 α' (α' * U) δx (α' * δU) δω / α')
        (𝓝[>] 0)
        (𝓝 (ambientForm 1
              (fderiv ℝ (poincareEmbedding 1
                (Real.sqrt (g / Real.sqrt v * Real.sqrt (Q1 * Q5)))) (U, x) (δU, δx)) +
          ‖Real.sqrt (g / Real.sqrt v * Real.sqrt (Q1 * Q5)) • δω‖ ^ 2))) := by
  sorry

end Maldacena1999

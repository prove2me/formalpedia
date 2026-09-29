-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
-- name    : LanglandsTunnell.CubicInduction.integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ede257b3-f112-5615-b312-cb3e04e9b492
-- title:
--   Integrability of the Godement integrand against a GL₂ Jacquet integral
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the $p$-adic completion. Let $\mu_0,\mu_1 \colon F^\times \to \mathbb{C}^\times$ be locally constant characters whose absolute values are $\lvert\cdot\rvert^{\sigma_0}$, $\lvert\cdot\rvert^{\sigma_1}$ for reals $\sigma_1 < \sigma_0$, and let $\varphi$ lie in `principalSeries2 p μ`, i.e. $\varphi \colon GL_2(F) \to \mathbb{C}$ is locally constant, invariant under left translation by the unipotent matrices $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = \mu_0(a_0)\mu_1(a_1)\,(\lvert a_0\rvert/\lvert a_1\rvert)^{1/2}\varphi(g)$. Let $\varphi_0 \colon M_{2\times 3}(F) \to \mathbb{C}$ be locally constant with compact support, let $\lambda$ be a locally constant character of $F^\times$, and let $\varepsilon,\eta$ each be the standard additive character $\psi_p$ of $F$ or its inverse. Then for every Haar measure $\mu_2$ on $GL_2(F)$ and every $g \in GL_3(F)$, the function of $h \in GL_2(F)$ obtained as follows is $\mu_2$-integrable: set $\Phi(X,k) = \varphi_0(X)\int_F \varepsilon(x)\,\varphi(w\,n(x)\,k)\,dx$ with $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $dx$ the self-dual Haar measure; form $\Psi_h(X) = \Phi(Xg, h^{-1})$; take the partial Fourier transform of $\Psi_h$ in the last column, $\int_{F^2}\Psi_h(Y[u])\,\eta(u_1 Y_{0,2} + u_2 Y_{1,2})\,du$ with $Y[u]$ denoting $Y$ with last column replaced by $u$ and $du$ the product self-dual measure, evaluated at the $2\times 3$ matrix $Y$ whose first two columns are those of $h$ and whose last column is the column of index $1$ of $(h^{-1})^{\mathsf T}$; and multiply the result by $\lambda(\det h)$ and by the module of $\det h$ raised to the power $1/2$.
--
--   This is the local absolute-convergence statement for the Godement-section integrand entering the mixed-model $GL_3 \times GL_2$ Rankin–Selberg integral at a finite place, the inner $GL_2$ factor being the Jacquet integral of a principal-series vector in the chamber $\sigma_1 < \sigma_0$. It is used in the evaluation of the local Rankin–Selberg integral of the $GL_3$ Whittaker function in [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction NumberField.StandardAddChar

theorem LanglandsTunnell.CubicInduction.integrable_rowFourier23_jacquet_godementIntegrand_of_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (φ₀ : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → ℂ) (hφ₀ : IsLocallyConstant φ₀ ∧ HasCompactSupport φ₀)
    (lam0 : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlam0 : IsLocallyConstant lam0)
    (ε : AddChar (p.adicCompletion ℚ) ℂ) (hε : ε = psiLocal ℚ p ∨ ε = (psiLocal ℚ p)⁻¹)
    (η : AddChar (p.adicCompletion ℚ) ℂ) (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (g : LocalGL3 p),
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        rowFourier23 p η
            (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
                φ₀ X * ∫ x : p.adicCompletion ℚ, ε x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
              (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
            (godementArg p h)
          * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ)) μ₂ := by sorry

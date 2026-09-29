-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat
-- name    : NumberField.AdelicFourier.exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/8d45db0c-a993-5abc-9450-fe2a815e3af4
-- title:
--   Godement's estimate on GL₂(A_ℚ), small-norm half
-- statement:
--   Fix a Haar measure $\nu_0$ on the idele group $(\mathbb A_{\mathbb Q})^\times$ of $\mathbb Q$ (with its Borel structure), a function $\Phi\colon \mathbb A_{\mathbb Q}^2\to\mathbb C$ lying in `schwartzBruhat2 ℚ`, that is, in the $\mathbb C$-span of the products $x\mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on the square of the mixed space of $\mathbb Q$ and $h$ a locally constant, compactly supported function on the square of the finite adeles; fix reals $c,u$ with $0<c$, an element $t_0\in\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ and a real $M>2$. Then there exist $A\ge 0$ and $N\in\mathbb N$, depending only on these data, with the following property. Let $\Omega\subseteq(\mathbb A_{\mathbb Q})^\times$ be any fundamental domain, for $\nu_0$, of the image of $\mathbb Q^\times$ in the ideles, and let $h$ belong to the integrally windowed Siegel set `integralWindowedSiegelSet ℚ c u`, i.e. the finite part of $h$ lies in `finiteIntegralGL2`, the archimedean height $\mathrm{archHeight}(h_\infty)=\prod_v(|\det|/\mathrm{rowNormSq})(h_v)^{\mathrm{mult}(v)}$ is at least $c$, and at every infinite place $v$ the window quantity $\mathrm{xWindowSq}(h_v)$ is at most $u^2$; assume moreover $\|\det(h t_0)\|=1$ for the idelic norm (the module of the distributive Haar character). Then the function $t\mapsto\bigl(\sum_{\xi\in\mathbb Q^2\setminus\{0\}}\|\Phi(t\cdot \xi\,(ht_0))\|\bigr)\,\|t\|^M$, where $\xi$ is viewed as a row vector over the adeles and multiplied on the right by the matrix $ht_0$, is integrable on $\Omega\cap\{\|t\|\le 1\}$ and $$\int_{\Omega\cap\{\|t\|\le1\}}\Bigl(\sum_{\xi\neq0}\|\Phi(t\,\xi\,(ht_0))\|\Bigr)\|t\|^M\,d\nu_0(t)\;\le\;A\,\bigl(1+\mathrm{archHeight}(h_\infty)\bigr)^N.$$
--
--   This is the half of Godement's uniform estimate for the absolute theta series on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ that covers the range $\|t\|\le1$, the bound being polynomial in the archimedean height of the Siegel-set element and uniform in the choice of fundamental domain for $\mathbb Q^\times$. It feeds the convergence and growth estimates for Godement sections used in the Rankin–Selberg input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open NumberField.AdelicFourier
open NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel

theorem NumberField.AdelicFourier.exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat
    [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν₀.IsHaarMeasure]
    {Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (c u : ℝ) (hc : 0 < c) (t₀ : AdelicGL2 (𝓞 ℚ) ℚ) (M : ℝ) (hM : 2 < M) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
      ∀ Ω : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ)).range Ω ν₀ →
      ∀ h ∈ integralWindowedSiegelSet ℚ c u,
        ideleNorm ℚ (Matrix.GeneralLinearGroup.det (h * t₀)) = 1 →
        IntegrableOn (fun t : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
            (∑' ξ : {ξ : Fin 2 → ℚ // ξ ≠ 0},
                ‖Φ ((t : AdeleRing (𝓞 ℚ) ℚ) •
                    Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 i))
                      ((h * t₀ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖)
              * (ideleNorm ℚ t) ^ M)
          (Ω ∩ {t | ideleNorm ℚ t ≤ 1}) ν₀ ∧
        ∫ t in Ω ∩ {t | ideleNorm ℚ t ≤ 1},
            (∑' ξ : {ξ : Fin 2 → ℚ // ξ ≠ 0},
                ‖Φ ((t : AdeleRing (𝓞 ℚ) ℚ) •
                    Matrix.vecMul (fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 i))
                      ((h * t₀ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖)
              * (ideleNorm ℚ t) ^ M ∂ν₀
          ≤ A * (1 + archHeight ℚ (AdelicLevel.glArch (𝓞 ℚ) ℚ h)) ^ N := by sorry

-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
-- name    : NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9f388751-763c-5492-8946-f7342857deef
-- title:
--   Non-negative Schwartz–Bruhat majorant for the reflected Fourier transform
-- statement:
--   Let $F$ be a number field, and equip its adele ring $\mathbb{A}=\mathbb{A}_F$ with a measurable space structure which is the Borel structure of its topology; let $\mu_1$ be an additive Haar measure on $\mathbb{A}$, let $\psi\colon\mathbb{A}\to\mathbb{C}^\times$ be an additive character which is trivial on the image of $F$, continuous and non-trivial, and let $\Phi\colon\mathbb{A}^2\to\mathbb{C}$ lie in `schwartzBruhat2 F`, the $\mathbb{C}$-span of the pure tensors $x\mapsto g((x_i)_\infty)\,h((x_i)_{\mathrm{fin}})$ with $g$ a Schwartz function on two copies of the mixed space of $F$ and $h$ locally constant with compact support on two copies of the finite adele ring. Write $\Phi'=$ `reflectPair` $\psi\,\mu_1\,\Phi$, that is $\Phi'(x)=\widehat{\Phi}(x_1,-x_0)$, where $\widehat{\Phi}$ is the Fourier integral of $\Phi$ with respect to the character `pairChar` $\psi$ and the measure `pairHaar` $\mu_1$ on $\mathbb{A}^2$. Then there exists $\Psi\in$ `schwartzBruhat2 F` such that $\Psi$ takes real non-negative values (for all $x$, $\operatorname{Re}\Psi(x)\ge 0$ and $\operatorname{Im}\Psi(x)=0$), such that $\|\Phi'(x)\|\le\operatorname{Re}\Psi(x)$ for every $x\in\mathbb{A}^2$, and such that for every measurable space $T$, every measure $\tau$ on $T$, every map $\mathrm{col}\colon T\to\mathbb{A}^2$, every $N\colon T\to\mathbb{R}$ with $\{t\mid 1\le N(t)\}$ measurable, and every real $s\ge 0$, the $[0,\infty]$-valued integrals satisfy $$\int_{\{t\,:\,1\le N(t)\}}\|\Phi'(\mathrm{col}\,t)\|\,d\tau\;\le\;\int_T \operatorname{Re}\Psi(\mathrm{col}\,t)\cdot N(t)^{s}\,d\tau,$$ with $N(t)^s$ the real power and both factors read through `ENNReal.ofReal`.
--
--   This is the majorisation step used in the Godement–Jacquet style analysis of zeta integrals: the tail integral of the reflected Fourier transform of a Schwartz–Bruhat function over the region where a norm function is at least $1$ is bounded by a genuine zeta integral $\int\Psi(\mathrm{col}\,t)N(t)^{s}\,d\tau$ of a non-negative Schwartz–Bruhat function at any exponent $s\ge 0$. It feeds the convergence statement for the twisted centralizer integral used in the Godement section of the automorphic-form development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier AutomorphicForm
open scoped ENNReal

theorem NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ, Ψ ∈ schwartzBruhat2 F ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, 0 ≤ (Ψ x).re ∧ (Ψ x).im = 0) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, ‖reflectPair ψ μ₁ Φ x‖ ≤ (Ψ x).re) ∧
      ∀ (T : Type) [MeasurableSpace T] (τ : Measure T) (col : T → (Fin 2 → AdeleRing (𝓞 F) F))
        (N : T → ℝ), MeasurableSet {t | 1 ≤ N t} → ∀ s : ℝ, 0 ≤ s →
          ∫⁻ t in {t | 1 ≤ N t}, ‖reflectPair ψ μ₁ Φ (col t)‖ₑ ∂τ ≤
            ∫⁻ t, ENNReal.ofReal (Ψ (col t)).re * ENNReal.ofReal (N t ^ s) ∂τ := by sorry

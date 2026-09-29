-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_forall_setIntegral_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet
-- name    : NumberField.AdelicFourier.exists_forall_setIntegral_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/8b5e8e2d-0418-5984-af94-e3e0a67fb919
-- title:
--   Godement's bound for the truncated theta integral on a Siegel set
-- statement:
--   Let $F$ be a number field with adele ring $\mathbb{A}$, let $\nu_0$ be a Haar measure on the idele group $\mathbb{A}^\times$ (with its Borel structure), and let $\Phi \colon \mathbb{A}^2 \to \mathbb{C}$ lie in `schwartzBruhat2 F`, the $\mathbb{C}$-span of the pure tensors $x \mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on $(\text{mixed space of } F)^2$ and $h$ a locally constant, compactly supported function on $(\text{finite adeles})^2$. Fix reals $c>0$ and $u$, an element $t_0 \in \mathrm{GL}_2(\mathbb{A})$ and a real exponent $M$. The assertion: there exist $A \ge 0$ and $N \in \mathbb{N}$ such that for every set $\Omega \subseteq \mathbb{A}^\times$ which is a fundamental domain for the image of $F^\times$ in $\mathbb{A}^\times$ with respect to $\nu_0$, and every $h$ in `integralWindowedSiegelSet F c u` — i.e. with finite part in $\mathrm{GL}_2$ of level-zero integral type, archimedean height $\prod_v (|\det|/\mathrm{rowNormSq})^{\mathrm{mult}(v)} \ge c$, and $x$-window $\mathrm{topNormSq}/\mathrm{rowNormSq} - \mathrm{localHeight}^2 \le u^2$ at each infinite place — satisfying $\|\det(h t_0)\| = 1$ for the idelic norm (the module of the distributive Haar character), the function $t \mapsto \bigl(\sum_{\xi \in F^2 \setminus \{0\}} \|\Phi(t \cdot \xi (h t_0))\|\bigr)\|t\|^M$, with $\xi$ a row vector mapped into $\mathbb{A}^2$ and the inner sum an unconditional sum of non-negative reals, is integrable on $\Omega \cap \{\|t\| \ge 1\}$ and its integral there is at most $A\,(1 + H_\infty(h))^N$, where $H_\infty(h)$ is the archimedean height of the archimedean part of $h$.
--
--   This is Godement's estimate for the truncated theta integral attached to a Schwartz–Bruhat function on $\mathbb{A}^2$: the growth in the height is polynomial, uniformly over the Siegel set and over the choice of fundamental domain for the principal ideles. It is the analytic input used to show that the Godement–Eisenstein series on $\mathrm{GL}_2$, once its polar part is subtracted, is entire and uniformly Siegel-bounded, in the Rankin–Selberg part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_forall_setIntegral_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm
open AutomorphicForm.WindowedSiegel

theorem NumberField.AdelicFourier.exists_forall_setIntegral_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F)
    (c u : ℝ) (hc : 0 < c) (t₀ : AdelicGL2 (𝓞 F) F) (M : ℝ) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν₀ →
      ∀ h ∈ integralWindowedSiegelSet F c u,
        ideleNorm F (Matrix.GeneralLinearGroup.det (h * t₀)) = 1 →
        IntegrableOn (fun t : (AdeleRing (𝓞 F) F)ˣ =>
            (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
                ‖Φ ((t : AdeleRing (𝓞 F) F) •
                    Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                      ((h * t₀ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖)
              * (ideleNorm F t) ^ M)
          (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ ∧
        ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t},
            (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
                ‖Φ ((t : AdeleRing (𝓞 F) F) •
                    Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                      ((h * t₀ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖)
              * (ideleNorm F t) ^ M ∂ν₀
          ≤ A * (1 + archHeight F (AdelicLevel.glArch (𝓞 F) F h)) ^ N := by sorry

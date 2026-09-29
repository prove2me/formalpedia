-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
-- name    : NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/a4f1cf80-0aea-5365-af26-5a8e4fa5822b
-- title:
--   Adelic theta transformation formula on GL₂
-- statement:
--   Let $F$ be a number field, with its adele ring $\mathbb{A}=\mathbb{A}_F$ carrying a Borel measurable structure, and let $\mu_1$ be an additive Haar measure on $\mathbb{A}$ normalised so that the adelic box — the set of adeles whose infinite component lies in the preimage, under the identification of $\mathbb{A}_\infty$ with the mixed space, of the fundamental domain of the lattice basis of $F$, and whose finite component is integral at every height-one prime of $\mathcal{O}_F$ — has measure $1$. Let $\psi$ be an additive character of $\mathbb{A}$ with values in $\mathbb{C}$ which is continuous, non-trivial, and satisfies $\psi(\alpha)=1$ for every $\alpha\in F$ embedded in $\mathbb{A}$. Let $\Phi:\mathbb{A}^2\to\mathbb{C}$ lie in `schwartzBruhat2 F`, the $\mathbb{C}$-span of the pure tensors $x\mapsto g\bigl((x_i)_\infty\bigr)\,h\bigl((x_i)_{\mathrm{fin}}\bigr)$ with $g$ a Schwartz function on $(\text{mixed space})^2$ and $h$ a locally constant, compactly supported function on $(\mathbb{A}_{\mathrm{fin}})^2$. Let $g\in\mathrm{GL}_2(\mathbb{A})$ and let $t\in\mathbb{A}^\times$. Writing $\|\cdot\|$ for the idele norm, defined as the value of the distributive Haar character of $\mathbb{A}$, and $\Phi'=$ `reflectPair` $\psi\,\mu_1\,\Phi$, i.e. $\Phi'(x)=\widehat{\Phi}(x_1,-x_0)$ with $\widehat{\Phi}$ the two-variable adelic Fourier transform taken with respect to the character $\psi$ and the product measure $\mu_1\times\mu_1$, the asserted identity is
--   $$\sum_{\xi\in F^2,\ \xi\neq 0}\Phi\bigl(t\cdot(\xi g)\bigr)+\Phi(0)=\|t\|^{-2}\Bigl(\|\det g\|^{-1}\sum_{\xi\in F^2,\ \xi\neq 0}\Phi'\bigl(t^{-1}(\det g)^{-1}\cdot(\xi g)\bigr)+\|\det g\|^{-1}\Phi'(0)\Bigr),$$
--   where $\xi$ is regarded as a row vector in $\mathbb{A}^2$ through the diagonal embedding of $F$, $\xi g$ denotes the row-vector product, $\|t\|^{-2}$ is the complex power with exponent $-(2:\mathbb{C})$, and the two sums are unconditional sums over the subtype of non-zero elements of $F^2$ (no summability claim is part of the conclusion).
--
--   This is the theta transformation formula for the theta series $\Theta(t,g)=\sum_{\xi\neq 0}\Phi(t\,\xi g)$ attached to a two-variable adelic Schwartz–Bruhat function, i.e. Poisson summation on $\mathbb{A}^2$ for the translate and dilate $x\mapsto\Phi(t\,xg)$ rewritten via the reflected Fourier transform $\Phi'$. It feeds the analytic continuation and functional equation of Godement–Eisenstein series and of Rankin–Selberg integrals for $\mathrm{GL}_2$ over $F$, and is used in the growth estimates for adelic zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal AutomorphicForm

theorem NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox F) = 1)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F)
    (g : AdelicGL2 (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ ((t : AdeleRing (𝓞 F) F) •
          Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
            (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
      + Φ 0 =
    ((ideleNorm F t : ℝ) : ℂ) ^ (-(2 : ℂ)) *
      ((((ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ) *
          ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            reflectPair ψ μ₁ Φ (((t⁻¹ * (Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
                AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
        + (((ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ) * reflectPair ψ μ₁ Φ 0) := by sorry

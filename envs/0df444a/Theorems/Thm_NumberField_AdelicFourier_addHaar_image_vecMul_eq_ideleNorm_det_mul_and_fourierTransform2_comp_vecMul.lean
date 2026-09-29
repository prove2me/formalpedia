-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
-- name    : NumberField.AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/fdb98d8a-ec81-525b-aa5e-bc1f277b9cf1
-- title:
--   Module of GL₂(A_F) acting on adelic row vectors
-- statement:
--   Let $F$ be a number field, let its adele ring $\mathbb{A}_F$ carry a measurable space structure which is the Borel structure of its topology, and let $g$ be an element of $\mathrm{GL}_2(\mathbb{A}_F)$, acting on row vectors $x \in \mathbb{A}_F^2$ by $x \mapsto x g$ (`Matrix.vecMul` with the matrix underlying $g$). Write $\chi(\det g) =$ `distribHaarChar` $(\mathbb{A}_F)(\det g) \in \mathbb{R}_{\ge 0}$ for the factor by which multiplication by the idele $\det g$ scales additive Haar measure on $\mathbb{A}_F$, and $\|\det g\| =$ `ideleNorm` $F(\det g)$ for the same quantity viewed as a real number. Four assertions are made, each for every additive Haar measure. (i) The push-forward of an additive Haar measure $\mu$ on $\mathbb{A}_F^2$ along $x \mapsto x g$ equals $\chi(\det g)^{-1} \cdot \mu$. (ii) For every, not necessarily measurable, set $s \subseteq \mathbb{A}_F^2$, $\mu(s g) = \chi(\det g)\,\mu(s)$. (iii) For every $f \colon \mathbb{A}_F^2 \to \mathbb{C}$, the function $x \mapsto f(xg)$ is $\mu$-integrable if and only if $f$ is, and $\int f(xg)\,d\mu = \|\det g\|^{-1} \int f\,d\mu$ (Bochner integrals, so both sides vanish in the non-integrable case). (iv) For every additive Haar measure $\mu_1$ on $\mathbb{A}_F$, every additive character $\psi \colon \mathbb{A}_F \to \mathbb{C}^{\times}$, every $\Phi \colon \mathbb{A}_F^2 \to \mathbb{C}$ and every $y \in \mathbb{A}_F^2$, the two-variable Fourier transform $\widehat{\Phi}(w) = \int_{\mathbb{A}_F^2} \psi(-(v_0w_0 + v_1w_1))\,\Phi(v)\,d(\mu_1 \otimes \mu_1)(v)$ satisfies $\widehat{\Phi(\cdot\, g)}(y) = \|\det g\|^{-1}\,\widehat{\Phi}(g^{-1}y)$, where $g^{-1}y$ is the matrix of $g^{-1}$ applied to the column vector $y$.
--
--   This is the change-of-variables formula for the action of $\mathrm{GL}_2(\mathbb{A}_F)$ on $\mathbb{A}_F^2$, expressing the module of the action as the idelic norm of the determinant, together with the resulting equivariance of the two-variable adelic Fourier transform. It underlies the transformation law of adelic theta series $\sum_{\xi \in F^2} \Phi(t\xi g)$ under Poisson summation and the appearance of the factor $\|\det g\|^{\pm s}$ in Godement sections; it is cited in the computation of push-forwards of Haar measure under $\mathrm{GL}_2$-translation and in the theta-inversion statement for Schwartz–Bruhat functions of two adelic variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.lean

import Definitions.Def_AutomorphicForm_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier

theorem NumberField.AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure],
      Measure.map (fun x => Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) μ
        = (distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g))⁻¹ • μ) ∧
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
      (s : Set (Fin 2 → AdeleRing (𝓞 F) F)),
      μ ((fun x => Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) '' s)
        = distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g) * μ s) ∧
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
      (f : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ),
      (Integrable (fun x => f (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) μ ↔
          Integrable f μ) ∧
      ∫ x, f (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ∂μ
        = (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ)
            * ∫ x, f x ∂μ) ∧
    (∀ (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
      (y : Fin 2 → AdeleRing (𝓞 F) F),
      fourierTransform2 ψ μ₁
          (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) y
        = (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ)
            * fourierTransform2 ψ μ₁ Φ
                (Matrix.mulVec ((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
                    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) y)) := by sorry

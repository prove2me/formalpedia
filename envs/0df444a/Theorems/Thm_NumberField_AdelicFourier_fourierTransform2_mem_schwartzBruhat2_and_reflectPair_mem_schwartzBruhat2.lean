-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
-- name    : NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/7b330fab-988f-5129-94f5-85217d3dd16f
-- title:
--   Schwartz–Bruhat space of pairs is stable under adelic Fourier transform
-- statement:
--   Let $F$ be a number field, with its adele ring $\mathbb{A}=\mathbb{A}_F$ carrying a measurable structure that is the Borel structure of its topology, and let $\mu_1$ be an additive Haar measure on $\mathbb{A}$. Let $\psi : \mathbb{A} \to \mathbb{C}$ be an additive character which is global in the sense of the predicate `IsGlobalAddChar`: it is trivial on the image of $F$ under $\mathbb{A}$'s structure map, continuous, and not the trivial character. Let $\Phi : \mathbb{A}^2 \to \mathbb{C}$ (functions on `Fin 2 →`$\mathbb{A}$) lie in `schwartzBruhat2 F`, the $\mathbb{C}$-submodule spanned by the pure tensors $x \mapsto g\bigl((x_i)_\infty\bigr)_{i}\cdot h\bigl((x_i)_{\mathrm{f}}\bigr)_{i}$, where $g$ is a Schwartz function on the two-fold product of the mixed space of $F$ (the archimedean components being transported along the ring isomorphism of $\mathbb{A}_\infty$ with the mixed space) and $h$ is a locally constant, compactly supported function on the two-fold product of the finite adele ring. Then both the two-variable Fourier transform $\widehat{\Phi}(w) = \int_{\mathbb{A}^2} \psi\bigl(-(v_0w_0 + v_1w_1)\bigr)\,\Phi(v)\,\mathrm{d}(\mu_1\times\mu_1)(v)$, formed with the character $u \mapsto \psi(u_0+u_1)$ of $\mathbb{A}^2$ and the product measure, and the reflected function $x \mapsto \widehat{\Phi}(x_1, -x_0)$ again belong to `schwartzBruhat2 F`.
--
--   This is the two-variable case of the stability of the Schwartz–Bruhat space of the adeles under Fourier transform, together with the stability under the reflection $(x_0,x_1)\mapsto(x_1,-x_0)$ coming from the Weyl element of $\mathrm{GL}_2$. It underlies the Godement-section and Whittaker-coefficient computations, where Poisson summation over a pair of adelic variables is applied to $\Phi$ and to its reflection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicFourier
open AutomorphicForm

theorem NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    fourierTransform2 ψ μ₁ Φ ∈ schwartzBruhat2 F ∧ reflectPair ψ μ₁ Φ ∈ schwartzBruhat2 F := by sorry

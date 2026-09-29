-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
-- name    : NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/04124890-f33a-5917-8d38-5a55e5b984c5
-- title:
--   Fourier transform preserves the adelic Schwartz–Bruhat space
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F$ (`AdeleRing (𝓞 F) F`) equipped with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$. Let $\psi$ be an additive character $\mathbb{A}_F \to \mathbb{C}^{\times}$ which is global in the sense of `IsGlobalAddChar`: it is trivial on the principal adeles, i.e. $\psi(\alpha) = 1$ for every $\alpha$ in the image of $F \to \mathbb{A}_F$, it is continuous, and it is not the trivial character. Let $f : \mathbb{A}_F \to \mathbb{C}$ belong to `schwartzBruhat F`, the $\mathbb{C}$-linear span inside $\mathbb{A}_F \to \mathbb{C}$ of the set of pure tensors, namely of those functions of the form $x \mapsto g\big(\rho(x_\infty)\big)\, h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ of $F$, $\rho$ the ring isomorphism from the infinite adeles onto that mixed space, and $h : \mathbb{A}_{F,\mathrm{fin}} \to \mathbb{C}$ locally constant with compact support. Then the function $w \mapsto \int_{\mathbb{A}_F} \psi(-(vw)) f(v)\,d\mu(v)$ again belongs to `schwartzBruhat F`. No formula for the transform is asserted, and $\mu$ is an arbitrary additive Haar measure, not a normalised one.
--
--   This is the stability of the adelic Schwartz–Bruhat space under the Fourier transform attached to a global additive character, as in Tate's thesis. It underlies the adelic harmonic analysis used in the treatment of automorphic forms on $\mathrm{GL}_2$ over a number field, where Whittaker coefficients and approximation arguments for automorphic functions require that Fourier transforms stay within the Schwartz–Bruhat class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F := by sorry

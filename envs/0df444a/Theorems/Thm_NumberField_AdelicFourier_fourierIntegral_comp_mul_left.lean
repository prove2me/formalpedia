-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
-- name    : NumberField.AdelicFourier.fourierIntegral_comp_mul_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/f7b55f44-7ff6-5a88-9326-783367fecc56
-- title:
--   Dilation rule for the adelic Fourier transform
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F$ = `AdeleRing (𝓞 F) F` equipped with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$, that is, a homomorphism from the additive group of $\mathbb{A}_F$ to the multiplicative monoid of $\mathbb{C}$ (no continuity or non-degeneracy is assumed), let $f : \mathbb{A}_F \to \mathbb{C}$ be an arbitrary function (no integrability or measurability is assumed), let $a$ be a unit of the ring $\mathbb{A}_F$, i.e. an idèle, and let $w \in \mathbb{A}_F$. Writing $\mathcal{F}_{\psi,\mu}g(w) = \int \psi(-(v w))\, g(v)\,d\mu(v)$ for the transform `fourierIntegral ψ μ g`, the assertion is
--   $$\mathcal{F}_{\psi,\mu}\bigl(v \mapsto f(a v)\bigr)(w) = \bigl(\operatorname{distribHaarChar}(\mathbb{A}_F)(a)\bigr)^{-1}\, \mathcal{F}_{\psi,\mu} f\bigl(a^{-1} w\bigr),$$
--   where the scalar is the positive real value at $a$ of Mathlib's distributive Haar character for the action of $\mathbb{A}_F^{\times}$ on the additive group $\mathbb{A}_F$ — the adelic modulus $|a|_{\mathbb{A}}$ — coerced into $\mathbb{C}$ and inverted.
--
--   This is the dilation (or stretching) rule of Tate's adelic Fourier analysis: composing with multiplication by an idèle $a$ scales the Fourier transform by $|a|_{\mathbb{A}}^{-1}$ and translates its argument by $a^{-1}$. It is used in the Fourier-inversion statement for pure tensors of test functions and in the estimates for sums of automorphic test functions over unipotent translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier

theorem NumberField.AdelicFourier.fourierIntegral_comp_mul_left (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) := by sorry

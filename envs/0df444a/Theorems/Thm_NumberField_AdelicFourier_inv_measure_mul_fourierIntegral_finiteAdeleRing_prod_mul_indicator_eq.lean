-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
-- name    : NumberField.AdelicFourier.inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/729949cf-a399-5681-b02a-537e2efc6a7e
-- title:
--   Factorisation of the finite-adelic Fourier transform of an S-standard function
-- statement:
--   Let $F$ be a number field, and equip the finite adele ring $\mathbb{A}_F^{f} =$ `FiniteAdeleRing (𝓞 F) F` and each completion $F_v$ ($v$ running over the height-one spectrum of $\mathcal{O}_F$) with measurable structures that are the Borel structures of their topologies; let $\nu$ be an additive Haar measure on $\mathbb{A}_F^{f}$ and, for each $v$, let $\mu_v$ be an additive Haar measure on $F_v$. Let $\psi_f$ be a continuous additive character $\mathbb{A}_F^{f} \to \mathbb{C}$ and, for each $v$, $\psi_v$ a continuous additive character $F_v \to \mathbb{C}$, such that $\psi_f(x) = \prod^{\mathrm{f}}_v \psi_v(x_v)$ (finprod) for every adele $x$, and such that, for all but finitely many $v$, $\psi_v(z) = 1$ for every $z$ in the valuation ring $\mathcal{O}_v =$ `v.adicCompletionIntegers F`. Let $S$ be a finite set of places, and $h_v : F_v \to \mathbb{C}$ a family of functions that, for $v \in S$, are locally constant with compact support. Then for every $w \in \mathbb{A}_F^{f}$, writing $\mathcal{F}_{\psi,\mu}f(w) = \int \psi(-(x w)) f(x)\,d\mu(x)$ and letting $H(x) = \bigl(\prod_{v \in S} h_v(x_v)\bigr) \cdot \mathbf{1}[x_v \in \mathcal{O}_v \text{ for all } v \notin S]$, one has $$\nu\bigl(\{x : x_v \in \mathcal{O}_v \ \forall v\}\bigr)^{-1}\,\mathcal{F}_{\psi_f,\nu}H(w) = \Bigl(\prod_{v \in S} \mu_v(\mathcal{O}_v)^{-1}\,\mathcal{F}_{\psi_v,\mu_v}h_v(w_v)\Bigr)\cdot \mathbf{1}\bigl[\psi_v(z w_v) = 1 \text{ for all } v \notin S \text{ and all } z \in \mathcal{O}_v\bigr],$$ the measures of the integral box and of the local rings being taken as real numbers and coerced into $\mathbb{C}$, and the indicators being $1$ or $0$ according as the stated condition holds or fails.
--
--   This is the finite-adelic case of the statement that the Fourier transform of a factorisable function factorises place by place, in the normalisation in which one divides by the volumes of the integral boxes, so that no identification of $\nu$ with a tensor product of the $\mu_v$ is needed and the off-$S$ local factors collapse into a single indicator for the dual condition $w_v \in \mathcal{O}_v^{\perp}$. It is used in the construction of Schwartz–Bruhat test functions with prescribed local behaviour and in the verification of the Hecke datum entering the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory
open scoped Classical

theorem NumberField.AdelicFourier.inv_measure_mul_fourierIntegral_finiteAdeleRing_prod_mul_indicator_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ) (hψf : Continuous ψf)
    (ψv : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ) (hψv : ∀ v, Continuous (ψv v))
    (hprod : ∀ x : FiniteAdeleRing (𝓞 F) F, ψf x = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (hunr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v z = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (w : FiniteAdeleRing (𝓞 F) F) :
    ((ν.real (integralFiniteAdeles (𝓞 F) F) : ℂ))⁻¹ *
        fourierIntegral ψf ν
          (fun x => (∏ v ∈ S, h v (x v)) *
            (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then 1 else 0)) w
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ))⁻¹ *
            fourierIntegral (ψv v) (μ v) (h v) (w v)) *
        (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
              ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψv v (z * w v) = 1
          then 1 else 0) := by sorry

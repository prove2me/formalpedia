-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply
-- name    : NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/43c6674a-5b90-5c0c-80a6-ca884e6c8e0c
-- title:
--   Finite-adelic Fourier transform of a principal coset indicator
-- statement:
--   Let $F$ be a number field, with the finite adele ring $\mathbb{A}_F^f =$ `FiniteAdeleRing (𝓞 F) F` equipped with a measurable space structure that is the Borel structure of its topology, let $\nu$ be an additive Haar measure on $\mathbb{A}_F^f$, let $\psi_f \colon \mathbb{A}_F^f \to \mathbb{C}$ be a continuous additive character, let $d \in \mathcal{O}_F$ be nonzero, let $k \in F$, and let $w \in \mathbb{A}_F^f$. Write $\widehat{\mathcal{O}}_F$ for `integralFiniteAdeles (𝓞 F) F`, the set of finite adeles $x$ with $x_v$ in the valuation ring of $F_v$ for every $v$ in the height-one spectrum of $\mathcal{O}_F$, and let $S$ be the image of $\widehat{\mathcal{O}}_F$ under $z \mapsto k + d\,z$, the images of $k$ and $d$ in $\mathbb{A}_F^f$ being taken along the structure map from $F$. Then the Fourier integral of the $\mathbb{C}$-valued indicator function of $S$ (the indicator of $S$ with values the constant function $1$), namely $\int_{\mathbb{A}_F^f} \psi_f(-(v w))\,\mathbf{1}_S(v)\, d\nu(v)$, equals $\psi_f(-(k w)) \cdot \nu(S)^{\mathbb{R}} \cdot \varepsilon$, where $\nu(S)^{\mathbb{R}}$ is the real number attached to the measure $\nu(S)$, viewed in $\mathbb{C}$, and $\varepsilon$ is $1$ if $\psi_f(d\,w\,z) = 1$ for all $z \in \widehat{\mathcal{O}}_F$, and $0$ otherwise.
--
--   This is the basic local-to-global computation of Tate's thesis in the finite-adelic setting: the Fourier transform of the characteristic function of a principal coset $k + d\widehat{\mathcal{O}}_F$ is, up to the translation factor $\psi_f(-kw)$ and the volume of the coset, the characteristic function of the set of $w$ for which $\psi_f$ is trivial on $d\,w\,\widehat{\mathcal{O}}_F$. It is used in [`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq`](thm.html#NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq), the finite-adelic Fourier inversion step for such indicator functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
open scoped Classical in

theorem NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν
        (((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator 1)
        w
      = ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k * w))
        * ((ν ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
              ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w * z) = 1
            then 1 else 0) := by sorry

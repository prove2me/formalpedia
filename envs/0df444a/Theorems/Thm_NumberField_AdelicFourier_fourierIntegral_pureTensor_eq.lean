-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
-- name    : NumberField.AdelicFourier.fourierIntegral_pureTensor_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/00f86b1d-cc53-5223-b1e9-3997732b1509
-- title:
--   Product formula for the adelic Fourier transform of a pure tensor
-- statement:
--   Let $F$ be a number field, and fix a Borel measurable structure on the adele ring $\mathbb{A}_F$ together with an additive Haar measure $\mu$, and likewise a Borel measurable structure on the finite adele ring $\mathbb{A}_F^{f}$ with an additive Haar measure $\nu$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is continuous and satisfies $\|\psi(x)\| = 1$ for all $x$. Let $g$ be a Schwartz function on the mixed space $\mathrm{mixedSpace}\,F$ with values in $\mathbb{C}$, and let $h : \mathbb{A}_F^{f} \to \mathbb{C}$ be locally constant with compact support. Write $e$ for the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F` from the infinite adeles to the mixed space. Then for every $w \in \mathbb{A}_F$, the Fourier integral $\int \psi(-(v w))\, g(e(v_\infty))\, h(v_f)\, d\mu(v)$ of the pure tensor equals the product of three quantities: the real constant $\mu(B)$ divided by $\mathrm{covol}(\mathrm{integerLattice}\,F)\cdot\nu(\widehat{\mathcal O}_F)$, viewed in $\mathbb{C}$; the Fourier integral of $g$ against Lebesgue measure on the mixed space at the point $e(w_\infty)$, taken with respect to the character $x \mapsto \psi(e^{-1}(x), 0)$; and the Fourier integral of $h$ against $\nu$ at $w_f$, taken with respect to the character $y \mapsto \psi(0, y)$. Here $B$ is the set of adeles whose infinite component lies in the $e$-preimage of the fundamental domain of the lattice basis $\mathrm{latticeBasis}\,F$ and whose finite component is integral at every height one prime of $\mathcal{O}_F$, $\widehat{\mathcal O}_F$ denotes that same set of everywhere-integral finite adeles, and the covolume is that of $\mathrm{integerLattice}\,F$ with respect to Lebesgue measure.
--
--   This is the factorisation of the adelic Fourier transform of a function that is a pure tensor of an archimedean Schwartz function and a finite locally constant compactly supported function, as in Tate's thesis, made explicit with its normalisation constant relating the chosen Haar measures $\mu$, $\nu$ and Lebesgue measure on the mixed space. It is used in the construction and estimation of factorisable adelic test functions for automorphic forms on $\mathrm{GL}_2$, in particular in the comparison of sums over lattice points with integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Covolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.fourierIntegral_pureTensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ
        (fun x ↦ g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2) w
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ)
        * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            MeasureTheory.volume (g : mixedEmbedding.mixedSpace F → ℂ) (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
        * fourierIntegral
            (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν h w.2 := by sorry

-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
-- name    : NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/1ecdabfc-da45-5e3d-ba77-9d216fe600e8
-- title:
--   Finite-adelic Fourier transform preserves Schwartz–Bruhat functions
-- statement:
--   Let $F$ be a number field, equipped with a measurable space structure on its ring of finite adeles $\mathbb{A}_F^f =$ `FiniteAdeleRing (𝓞 F) F` which is a Borel structure for the topology, and let $\nu$ be an additive Haar measure on $\mathbb{A}_F^f$. Let $\psi$ be an additive character of the full adele ring $\mathbb{A}_F = \mathbb{A}_{F,\infty} \times \mathbb{A}_F^f$ with values in $\mathbb{C}$ which is global in the sense of `IsGlobalAddChar`: it is trivial on the image of $F$ under the structure map $F \to \mathbb{A}_F$, it is continuous, and it is not the trivial character. Assume moreover that $\psi$ is standard at the infinite places: for every $x \in \mathbb{A}_{F,\infty}$ one has $\psi(x,0) = \exp(2\pi i \,\mathrm{Tr}_{\mathbb{R}}(x))$, the trace being taken over $\mathbb{R}$ of the image of $x$ in the mixed space of $F$ under `InfiniteAdeleRing.ringEquiv_mixedSpace`, and the exponential being `Real.fourierChar`. Let $h : \mathbb{A}_F^f \to \mathbb{C}$ be locally constant with compact support. Then the function $w \mapsto \int_{\mathbb{A}_F^f} \psi_f(-(vw))\, h(v)\, d\nu(v)$, where $\psi_f$ denotes the composition of $\psi$ with the inclusion $z \mapsto (0,z)$ of $\mathbb{A}_F^f$ into $\mathbb{A}_F$, is again locally constant and has compact support.
--
--   This is the stability of the Schwartz–Bruhat space of the finite adeles — locally constant compactly supported functions — under the Fourier transform attached to the finite part of a standard global additive character, in the style of Tate's thesis. It underlies the construction of the adelic Fourier transform on Schwartz–Bruhat functions, the adelic Fourier inversion statement for pure tensors, and integrability bounds used for unipotent terms in the cuspidality estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    IsLocallyConstant (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h)
      ∧ HasCompactSupport (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) := by sorry

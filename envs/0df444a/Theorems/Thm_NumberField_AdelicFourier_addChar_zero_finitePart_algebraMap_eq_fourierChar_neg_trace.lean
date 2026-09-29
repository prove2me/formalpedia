-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
-- name    : NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/280ab864-e68d-53d1-8a57-b695d85870c6
-- title:
--   Finite part of a trace-normalised global additive character at principal points
-- statement:
--   Let $F$ be a number field, and let $\psi$ be an additive character of the adele ring $\mathbb{A}_F$ (realised as the product of the infinite adele ring and the finite adele ring of $\mathcal{O}_F$ in $F$) with values in $\mathbb{C}$. Assume `IsGlobalAddChar F ψ`, that is: $\psi$ is trivial on principal adeles, $\psi(\mathrm{algebraMap}\,\alpha)=1$ for every $\alpha\in F$; $\psi$ is continuous; and $\psi$ is not the trivial character. Assume further the trace-normalisation at the archimedean places: for every $x$ in the infinite adele ring of $F$, $\psi(x,0)$ equals the value of `Real.fourierChar`, i.e. $\exp(2\pi i\,\cdot)$, at the trace over $\mathbb{R}$ of the image of $x$ under the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace F` onto the mixed space of $F$, viewed in $\mathbb{C}$. Then for every $q\in F$, the value of $\psi$ at the adele whose archimedean component is $0$ and whose finite component is the principal finite adele attached to $q$ is $$\psi(0,\iota_{\mathrm{f}}q)=\exp\bigl(-2\pi i\,\mathrm{Tr}_{F/\mathbb{Q}}(q)\bigr),$$ the rational trace being read as a real number.
--
--   This is the phase-conversion lemma for a trace-normalised standard additive character of $\mathbb{A}_F$ in the style of Tate's thesis: normalising $\psi$ at the infinite places determines its values at principal points of the finite part. It is used in the adelic Fourier-analytic part of the project, in particular in the identification of the trace dual by conditions on the finite part and in the adelic Poisson summation statements over boxes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace.lean

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

theorem NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (q : F) :
    ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar (-((Algebra.trace ℚ F q : ℚ) : ℝ)) : ℂ) := by sorry

-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet
-- name    : NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/afdc1457-5d9e-5f56-bfc2-652ff22f0d90
-- title:
--   Pure tensors are stable under dilation by nonzero elements of F
-- statement:
--   Let $F$ be a number field, let $a \in F$ be nonzero, and let $f : \mathbb{A}_F \to \mathbb{C}$ be a function on the adele ring of $F$ (formed from $\mathcal{O}_F$ and $F$) belonging to `pureTensorSet F`, that is: there are a Schwartz function $g$ on the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ attached to the mixed embedding of $F$, and a function $h$ on the finite adele ring of $F$ which is locally constant and has compact support, such that for all $x$ one has $f(x) = g\big(\mathrm{ringEquiv\_mixedSpace}_F(x_\infty)\big)\, h(x_{\mathrm{fin}})$, where $x_\infty$ and $x_{\mathrm{fin}}$ are the infinite and finite components of $x$ and $\mathrm{ringEquiv\_mixedSpace}_F$ is the ring isomorphism from the infinite adele ring to the mixed space. The conclusion is that the dilated function $x \mapsto f\big(\iota(a)\,x\big)$, where $\iota$ is the structure map $F \to \mathbb{A}_F$ embedding $a$ diagonally as a principal adele, again lies in `pureTensorSet F`, i.e. again factors as a Schwartz function of the infinite component times a locally constant compactly supported function of the finite component.
--
--   This is the dilation-invariance of the set of pure tensors in the adelic Schwartz–Bruhat space, as used in Tate's adelic Fourier analysis; multiplication by a principal idele preserves the product shape of a pure tensor. It is cited in the proof that the adelic Fourier integral of a Schwartz–Bruhat function is again Schwartz–Bruhat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.lean

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F] {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F := by sorry

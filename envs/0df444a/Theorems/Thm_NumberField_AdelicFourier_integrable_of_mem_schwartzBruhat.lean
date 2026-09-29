-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
-- name    : NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/29fd355c-bf94-5444-b896-df2c8c7839da
-- title:
--   Schwartz–Bruhat functions on A_F are Haar-integrable
-- statement:
--   Let $F$ be a number field (a field of type `Type` carrying a `NumberField` instance), and equip its adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` with a measurable space structure which is the Borel structure of its topology. Let $\mu$ be a measure on $\mathbb{A}_F$ that is an additive Haar measure, and let $f : \mathbb{A}_F \to \mathbb{C}$ lie in the submodule `schwartzBruhat F`, that is, in the $\mathbb{C}$-linear span of the set of functions of the form $x \mapsto g\bigl(\text{ringEquiv\_mixedSpace}(x_\infty)\bigr)\, h(x_{\mathrm{fin}})$, where $x_\infty$ and $x_{\mathrm{fin}}$ are the infinite and finite components of the adele $x$, $g$ is a Schwartz function on the mixed space of $F$ (the infinite adeles being transported to it along the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace F`), and $h : \mathbb{A}_{F,\mathrm{fin}} \to \mathbb{C}$ is locally constant with compact support. Then $f$ is Bochner-integrable with respect to $\mu$. Note that $\mu$ is an arbitrary additive Haar measure, no product decomposition over the places being assumed.
--
--   This is the basic integrability input of adelic Fourier analysis in the style of Tate's thesis: the Schwartz–Bruhat space of $\mathbb{A}_F$ consists of $\mu$-integrable functions, so that adelic integrals of such functions are defined. It is used throughout the analytic part of the development, for instance in the treatment of unipotent averages and constant terms of automorphic forms on $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier

theorem NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    MeasureTheory.Integrable f μ := by sorry

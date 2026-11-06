-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_actual_crt_product_assembly
-- name    : OAI.ActualEisensteinCubic.actual_crt_product_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:13:34.304537+00:00
-- url     : https://prove2.me/theorems/b20bd1af-21cd-46af-bfa5-fa66f07c581f
-- title:
--   Actual Eisenstein Cubic: actual crt product assembly
-- statement:
--   The Actual Eisenstein Cubic construction uses the actual crt product assembly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L430-L485
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L430-L485

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open AddChar MulChar

theorem OAI.ActualEisensteinCubic.actual_crt_product_assembly
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    [Fintype (O ⧸ ⨅ i, Ideal.span {p i})]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i}))
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
      Ideal.quotientInfRingEquivPiQuotient P (by
        intro i k hik
        exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik))
    (∑ z : O ⧸ ⨅ i, P i,
      ∏ i, localA5Kernel (P i) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (P i) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by sorry

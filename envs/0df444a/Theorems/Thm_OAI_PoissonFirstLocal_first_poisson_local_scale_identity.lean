-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_first_poisson_local_scale_identity
-- name    : OAI.PoissonFirstLocal.first_poisson_local_scale_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:13:31.687245+00:00
-- url     : https://prove2.me/theorems/d309d084-41c0-4fae-a671-95b05a9dc8a2
-- title:
--   Poisson First Local: first poisson local scale identity
-- statement:
--   The Poisson First Local construction uses the first poisson local scale identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L566-L578
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L566-L578

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
open OAI.PoissonFirstLocal

theorem OAI.PoissonFirstLocal.first_poisson_local_scale_identity
    (parityBit ε₁ ε₂ : Bool) (p : ℕ) :
    localC parityBit ε₁ ε₂ p * localCorrectionE parityBit ε₁ ε₂ p *
        (localJ2 parityBit ε₁ ε₂ p) ^ 2 =
      localA ε₁ p * localA ε₂ p * localS parityBit p := by sorry

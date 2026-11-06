-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_first_poisson_global_scale_identity
-- name    : OAI.PoissonFirstLocal.first_poisson_global_scale_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:14:46.915205+00:00
-- url     : https://prove2.me/theorems/98059386-6f42-409b-b86b-199023dfa6ad
-- title:
--   Poisson First Local: first poisson global scale identity
-- statement:
--   The Poisson First Local construction uses the first poisson global scale identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L580-L613
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L580-L613

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

theorem OAI.PoissonFirstLocal.first_poisson_global_scale_identity
    (P : Finset ℕ) (parityBit ε₁ ε₂ : ℕ → Bool) :
    (∏ p ∈ P, localC (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localJ2 (parityBit p) (ε₁ p) (ε₂ p) p) ^ 2 =
    (∏ p ∈ P, localA (ε₁ p) p) *
      (∏ p ∈ P, localA (ε₂ p) p) *
      (∏ p ∈ P, localS (parityBit p) p) := by sorry

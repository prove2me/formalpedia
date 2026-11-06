-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_first_prime_product_canonicalSextic
-- name    : OAI.ActualEisensteinCubic.first_prime_product_canonicalSextic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:16:31.194702+00:00
-- url     : https://prove2.me/theorems/ff794897-7e8f-4dbd-b476-d5ecbb650c7d
-- title:
--   Actual Eisenstein Cubic: first prime product canonical Sextic
-- statement:
--   The Actual Eisenstein Cubic construction uses the first prime product canonical Sextic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L389-L405
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L389-L405

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
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

theorem OAI.ActualEisensteinCubic.first_prime_product_canonicalSextic
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (S : Finset (O ⧸ P))
    (parityBit ε₁ ε₂ : O ⧸ P → Bool) (side : Bool) :
    (∏ z ∈ S,
      PoissonFirstLocal.oldFactorRing side
        (parityBit z) (ε₁ z) (ε₂ z) z
        (canonicalSextic P hgood)) =
      (canonicalSextic P hgood
        (∏ z ∈ S with
          PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      PoissonFirstLocal.quotientUnitMask
        (∏ z ∈ S with
          ¬PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z) := by sorry

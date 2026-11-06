-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_first_prime_product_identity_ring
-- name    : OAI.PoissonFirstLocal.first_prime_product_identity_ring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:16:23.98358+00:00
-- url     : https://prove2.me/theorems/f630a5b3-b701-4f94-8f2f-b4cdf507c888
-- title:
--   Poisson First Local: first prime product identity ring
-- statement:
--   The Poisson First Local construction uses the first prime product identity ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L200-L235
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L200-L235

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
open OAI.PoissonFirstLocal
open scoped Classical

theorem OAI.PoissonFirstLocal.first_prime_product_identity_ring
    {R : Type*} [CommRing R]
    (side : Bool) (P : Finset R)
    (parityBit ε₁ ε₂ : R → Bool)
    (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      (χ (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      quotientUnitMask
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z), z) := by sorry

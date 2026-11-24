-- Prove2me | Theorems.Thm_GlobalTheory_MonicSeparableProduct_exists_sep
-- name    : GlobalTheory.MonicSeparableProduct.exists_sep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:53.482161+00:00
-- url     : https://prove2.me/theorems/c82464b1-a4dd-445b-9216-6e6a7fca51d9
-- title:
--   Monic Separable Product: exists sep
-- statement:
--   The Monic Separable Product construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MonicEqProd.lean#L38-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MonicEqProd.lean#L38-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MonicEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MonicSeparableProduct
open Polynomial

theorem GlobalTheory.MonicSeparableProduct.exists_sep {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W)
    (hp : ∀ a : W, ¬IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p})
    (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W)
    (t : A) (ht : aug t = 0) :
    ∃ s b : A, IsUnit (aug s) ∧ s = b * s ^ 2 ∧
      ∀ P : Ideal A, P.IsPrime → algebraMap W A p ∈ P → s ∉ P → t ∈ P := by sorry

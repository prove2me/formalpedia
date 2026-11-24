-- Prove2me | Theorems.Thm_GlobalTheory_MonicSeparableProduct_monic_eq_prod
-- name    : GlobalTheory.MonicSeparableProduct.monic_eq_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:58.412188+00:00
-- url     : https://prove2.me/theorems/191f20b3-2402-4002-b34b-3adf7a6a394e
-- title:
--   Monic Separable Product: monic eq prod
-- statement:
--   The Monic Separable Product construction uses the monic eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MonicEqProd.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MonicEqProd.lean#L7-L36

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

theorem GlobalTheory.MonicSeparableProduct.monic_eq_prod {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) :
    ∀ (n : ℕ) (f : W[X]), f.Monic → f.natDegree = n →
      ∃ M : Multiset W, f = (M.map (fun r => X - C r)).prod := by sorry

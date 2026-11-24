-- Prove2me | Theorems.Thm_GlobalTheory_Mem_ImagQuad_exists_field_sq_eq_neg
-- name    : GlobalTheory.Mem.ImagQuad.exists_field_sq_eq_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:30.845022+00:00
-- url     : https://prove2.me/theorems/8a7370b0-9e98-4546-9e4a-4c6490e9b5ef
-- title:
--   Imag Quad: exists field sq eq neg
-- statement:
--   The Imag Quad construction uses the exists field sq eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsImagQuadIntegers.lean#L10-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsImagQuadIntegers.lean#L10-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.ImagQuad
open QuadraticZeta

theorem GlobalTheory.Mem.ImagQuad.exists_field_sq_eq_neg (d : ℕ) (hd : 0 < d) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (r : K),
      finrank ℚ K = 2 ∧ r ^ 2 = -(d : K) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_TriangularityLowCoeff_expOf_apply_le
-- name    : GlobalTheory.TriangularityLowCoeff.expOf_apply_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:05.903207+00:00
-- url     : https://prove2.me/theorems/2d2b154f-c400-46a9-9430-f212fbb9d996
-- title:
--   Triangularity Low Coeff: exp Of apply le
-- statement:
--   The Triangularity Low Coeff construction uses the exp Of apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L30-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial

theorem GlobalTheory.TriangularityLowCoeff.expOf_apply_le {d : ℕ} (L : List (Fin d)) (i : Fin d) : expOf L i ≤ L.length := by sorry

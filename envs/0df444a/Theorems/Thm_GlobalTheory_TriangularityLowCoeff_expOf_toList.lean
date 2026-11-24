-- Prove2me | Theorems.Thm_GlobalTheory_TriangularityLowCoeff_expOf_toList
-- name    : GlobalTheory.TriangularityLowCoeff.expOf_toList
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:22.482255+00:00
-- url     : https://prove2.me/theorems/dfb67f39-641c-4ed2-9ce3-541b721fa4c3
-- title:
--   Triangularity Low Coeff: exp Of to List
-- statement:
--   The Triangularity Low Coeff construction uses the exp Of to List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L34-L35

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

theorem GlobalTheory.TriangularityLowCoeff.expOf_toList {d : ℕ} (α : Fin d →₀ ℕ) : expOf (Finsupp.toMultiset α).toList = α := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_WeylInt_lowerTri_of_interlaced
-- name    : GlobalTheory.WeylInt.lowerTri_of_interlaced
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:39.720202+00:00
-- url     : https://prove2.me/theorems/838c2d67-7ee6-477b-a343-eeab96c2a47d
-- title:
--   Weyl Int: lower Tri of interlaced
-- statement:
--   The Weyl Int construction uses the lower Tri of interlaced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriIntegral.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriIntegral.lean#L9-L27

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.WeylInt
open Formalism.GradedWeylDivisibility

theorem GlobalTheory.WeylInt.lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_pairwise_positions
-- name    : GlobalTheory.CoeffWord.pairwise_positions
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:15:28.395936+00:00
-- url     : https://prove2.me/theorems/a8614a84-86e9-4dc7-b929-5aa225f9b7c5
-- title:
--   Coeff Word: pairwise positions
-- statement:
--   The Coeff Word construction uses the pairwise positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L158-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L158-L173

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}

theorem GlobalTheory.CoeffWord.pairwise_positions :
    (positions r n).Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_weight_colW
-- name    : GlobalTheory.CoeffWord.weight_colW
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:15:07.533889+00:00
-- url     : https://prove2.me/theorems/dcb9aa8a-4bcf-43a2-bbd3-5e7e528094d7
-- title:
--   Coeff Word: weight col W
-- statement:
--   The Coeff Word construction uses the weight col W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L215-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L215-L219

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

theorem GlobalTheory.CoeffWord.weight_colW (m : Fin r × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (colW r n) m s = ∑ a : Fin r, m (a, s) := by sorry

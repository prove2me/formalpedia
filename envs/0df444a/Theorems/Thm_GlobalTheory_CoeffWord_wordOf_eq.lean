-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_wordOf_eq
-- name    : GlobalTheory.CoeffWord.wordOf_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:15:32.408677+00:00
-- url     : https://prove2.me/theorems/762b35ba-a044-4185-aec9-984b59b2ab76
-- title:
--   Coeff Word: word Of eq
-- statement:
--   The Coeff Word construction uses the word Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L141-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L141-L156

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

theorem GlobalTheory.CoeffWord.wordOf_eq (e : Fin r × Fin n →₀ ℕ) : wordOf e = (positions r n).map (letter e) := by sorry

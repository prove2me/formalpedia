-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_single_monomial
-- name    : GlobalTheory.CoeffWord.single_monomial
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:29:04.225738+00:00
-- url     : https://prove2.me/theorems/371c30b1-2b7b-4e34-b105-6ce30c8f3df4
-- title:
--   Coeff Word: single monomial
-- statement:
--   The Coeff Word construction uses the single monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L20-L34

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

theorem GlobalTheory.CoeffWord.single_monomial (p : Fin r × Fin n) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    single R p (monomial m c) = Polynomial.monomial (m p) (monomial (m.erase p) c) := by sorry

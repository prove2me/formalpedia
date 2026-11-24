-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_unitri_monomial_of_lowerTri
-- name    : GlobalTheory.CoeffWord.unitri_monomial_of_lowerTri
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:15:28.254812+00:00
-- url     : https://prove2.me/theorems/efe0deec-5467-4683-9bb6-5557471dce2c
-- title:
--   Coeff Word: unitri monomial of lower Tri
-- statement:
--   The Coeff Word construction uses the unitri monomial of lower Tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L192-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L192-L204

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

theorem GlobalTheory.CoeffWord.unitri_monomial_of_lowerTri (m : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (c : R) :
    unitri R (positions r n) (monomial m c) = monomial (m.filter (· ∈ positions r n)) c := by sorry

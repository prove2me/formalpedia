-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_coeff_single
-- name    : GlobalTheory.CoeffWord.coeff_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:15:00.85368+00:00
-- url     : https://prove2.me/theorems/bab81fee-7cd9-40d2-b605-aa18f63c597c
-- title:
--   Coeff Word: coeff single
-- statement:
--   The Coeff Word construction uses the coeff single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L36-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L36-L58

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

theorem GlobalTheory.CoeffWord.coeff_single (p : Fin r × Fin n) (e : Fin r × Fin n →₀ ℕ) (he : e p = 0) (k : ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) :
    coeff e ((single R p G).coeff k) = coeff (e + Finsupp.single p k) G := by sorry

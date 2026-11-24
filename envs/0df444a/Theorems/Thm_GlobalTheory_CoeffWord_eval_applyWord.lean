-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_eval_applyWord
-- name    : GlobalTheory.CoeffWord.eval_applyWord
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:15:39.30981+00:00
-- url     : https://prove2.me/theorems/f1bf5558-d81f-40a7-a02d-7f3ccf569fa4
-- title:
--   Coeff Word: eval apply Word
-- statement:
--   The Coeff Word construction uses the eval apply Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L93-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L93-L131

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

theorem GlobalTheory.CoeffWord.eval_applyWord (e : Fin r × Fin n →₀ ℕ) (L : List (Fin r × Fin n))
    (h1 : ∀ q ∈ L, q.2.val < q.1.val) (h2 : L.Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val)
    (F : MvPolynomial (Fin r × Fin n) R) :
    eval (idFrame R r n) (applyWord R (L.map (letter e)) F) =
      coeff (e.filter (· ∈ L)) (unitri R L F) := by sorry

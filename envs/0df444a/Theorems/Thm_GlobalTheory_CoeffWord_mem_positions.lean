-- Prove2me | Theorems.Thm_GlobalTheory_CoeffWord_mem_positions
-- name    : GlobalTheory.CoeffWord.mem_positions
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:44.728527+00:00
-- url     : https://prove2.me/theorems/85b49396-797f-4ef0-800e-25a02e72c95c
-- title:
--   Coeff Word: mem positions
-- statement:
--   The Coeff Word construction uses the mem positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean#L137-L139

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

theorem GlobalTheory.CoeffWord.mem_positions (v : Fin r × Fin n) : v ∈ positions r n ↔ v.2.val < v.1.val := by sorry

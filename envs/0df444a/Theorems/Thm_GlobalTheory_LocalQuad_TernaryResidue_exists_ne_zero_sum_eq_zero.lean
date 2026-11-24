-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_TernaryResidue_exists_ne_zero_sum_eq_zero
-- name    : GlobalTheory.LocalQuad.TernaryResidue.exists_ne_zero_sum_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:43.858366+00:00
-- url     : https://prove2.me/theorems/f34bcd27-67a8-44aa-bde2-6fcb6dc3dc23
-- title:
--   Ternary Residue: exists ne zero sum eq zero
-- statement:
--   The Ternary Residue construction uses the exists ne zero sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitValuedTernaryLtOne.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitValuedTernaryLtOne.lean#L14-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.TernaryResidue
open MvPolynomial

theorem GlobalTheory.LocalQuad.TernaryResidue.exists_ne_zero_sum_eq_zero {k : Type*} [Field k] [Finite k] (a : Fin 3 → Fin 3 → k) :
    ∃ x : Fin 3 → k, x ≠ 0 ∧ ∑ i, ∑ j, a i j * x i * x j = 0 := by sorry

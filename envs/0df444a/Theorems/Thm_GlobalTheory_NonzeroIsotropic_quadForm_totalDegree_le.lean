-- Prove2me | Theorems.Thm_GlobalTheory_NonzeroIsotropic_quadForm_totalDegree_le
-- name    : GlobalTheory.NonzeroIsotropic.quadForm_totalDegree_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:34:56.028572+00:00
-- url     : https://prove2.me/theorems/1182011e-afe6-401c-9918-fd0b0d8ea9d9
-- title:
--   Nonzero Isotropic: quad Form total Degree le
-- statement:
--   The Nonzero Isotropic construction uses the quad Form total Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNonzeroIsotropic.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNonzeroIsotropic.lean#L9-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NonzeroIsotropic
open MvPolynomial

theorem GlobalTheory.NonzeroIsotropic.quadForm_totalDegree_le {k : Type u_1} [Field k] (a : Fin 3 → Fin 3 → k) :
    (∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by sorry

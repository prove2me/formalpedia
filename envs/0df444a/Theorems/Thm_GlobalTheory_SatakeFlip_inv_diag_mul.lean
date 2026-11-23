-- Prove2me | Theorems.Thm_GlobalTheory_SatakeFlip_inv_diag_mul
-- name    : GlobalTheory.SatakeFlip.inv_diag_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:36.78571+00:00
-- url     : https://prove2.me/theorems/2e2eff3a-1679-48f3-83b5-d2d4902f28e3
-- title:
--   Satake Flip: inv diag mul
-- statement:
--   The Satake Flip construction uses the inv diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsBorelSphRevInv.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsBorelSphRevInv.lean#L41-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix
open GlobalTheory GlobalTheory.SatakeFlip
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.SatakeFlip.inv_diag_mul {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) (i : Fin n) :
    (b⁻¹).val i i * b.val i i = 1 := by sorry

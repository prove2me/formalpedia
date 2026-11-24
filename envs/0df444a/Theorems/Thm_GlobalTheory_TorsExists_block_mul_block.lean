-- Prove2me | Theorems.Thm_GlobalTheory_TorsExists_block_mul_block
-- name    : GlobalTheory.TorsExists.block_mul_block
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:30.883098+00:00
-- url     : https://prove2.me/theorems/b88cb431-56ac-48b2-890e-d780b8649188
-- title:
--   Tors Exists: block mul block
-- statement:
--   The Tors Exists construction uses the block mul block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsIsUnitField.lean#L94-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsIsUnitField.lean#L94-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]

theorem GlobalTheory.TorsExists.block_mul_block {R : Type} [CommRing R] (P Q : Ix → Prop) [DecidablePred P] [DecidablePred Q]
    (M : Matrix Ix Ix R) (hM : M * M = 1) (h0 : ∀ p r, P p → ¬ Q r → M p r = 0) :
    M.submatrix (fun p : {p // P p} => p.1) (fun r : {r // Q r} => r.1) *
      M.submatrix (fun r : {r // Q r} => r.1) (fun p : {p // P p} => p.1) = 1 := by sorry

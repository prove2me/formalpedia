-- Prove2me | Theorems.Thm_GlobalTheory_Ex_QStr_exists_nsmul
-- name    : GlobalTheory.Ex.QStr.exists_nsmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:06:44.876933+00:00
-- url     : https://prove2.me/theorems/98b294dc-f846-4229-a3af-5779967604ed
-- title:
--   QStr: exists nsmul
-- statement:
--   The QStr construction uses the exists nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L185-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L185-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}

theorem GlobalTheory.Ex.QStr.exists_nsmul (hk : (k : C) ≠ 0) (y : N.X)
    (h : ∀ t : Multiplicative N.X →* Cˣ, t ^ k = 1 → t (Multiplicative.ofAdd y) = 1) : ∃ z : N.X, y = k • z := by sorry

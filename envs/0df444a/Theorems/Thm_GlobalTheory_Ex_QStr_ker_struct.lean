-- Prove2me | Theorems.Thm_GlobalTheory_Ex_QStr_ker_struct
-- name    : GlobalTheory.Ex.QStr.ker_struct
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:05:58.76333+00:00
-- url     : https://prove2.me/theorems/374b302f-d008-4f08-a635-a12aba42ad4f
-- title:
--   QStr: ker struct
-- statement:
--   The QStr construction uses the ker struct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L139-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L139-L183

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

theorem GlobalTheory.Ex.QStr.ker_struct (hk : (k : C) ≠ 0) (a : ℕ)
    (e : (powMonoidHom k : N.A →* N.A).ker ≃* Multiplicative (Fin a → ZMod k)) :
    Nonempty ((powMonoidHom k : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin (a + Module.finrank ℤ N.X) → ZMod k)) := by sorry

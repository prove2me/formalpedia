-- Prove2me | Theorems.Thm_GlobalTheory_Ex_QStr_orth_iff
-- name    : GlobalTheory.Ex.QStr.orth_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:06:29.131076+00:00
-- url     : https://prove2.me/theorems/1a02b7c1-a247-492c-b16c-30f26dfa0859
-- title:
--   QStr: orth iff
-- statement:
--   The QStr construction uses the orth iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L205-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L205-L228

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

theorem GlobalTheory.Ex.QStr.orth_iff (hk : (k : C) ≠ 0)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k) :
    (∀ p' : N.QT k, p'.1.1 = 1 → N.wp p p' = 1) ↔ ∃ p₀ : N.QT k, N.QEq p p₀ ∧ p₀.1.1 = 1 ∧ p₀.1.2.b = 1 := by sorry

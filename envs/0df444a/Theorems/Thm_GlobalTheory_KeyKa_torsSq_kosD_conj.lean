-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_torsSq_kosD_conj
-- name    : GlobalTheory.KeyKa.torsSq_kosD_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:50.014136+00:00
-- url     : https://prove2.me/theorems/0ea03338-7d76-4254-ac6b-d7d7bcde2a8a
-- title:
--   Key Ka: tors Sq kos D conj
-- statement:
--   The Key Ka construction uses the tors Sq kos D conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L165-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KosBlockMulKosD.lean#L165-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.torsSq_kosD_conj : ∀ (R : Type) [CommRing R] (g d : ℕ) (N : ℕ → ℕ) (m m' : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R) (B : ∀ j, (Matrix (Fin (N j)) (Fin (N j)) R)ˣ) (Pm : (Matrix (Fin d) (Fin d) R)ˣ) (t : Rˣ), (∀ i j, j < g → (B j).val * m' i j (j + 1) = m i j (j + 1) * (B (j + 1)).val) → Pm.val * ev' 0 = ev 0 * (B 0).val → IsCx kdeg (kosD m ev) → TorsSq kdeg (kosD m ev) (t : R) → ∃ t' : Rˣ, TorsSq kdeg (kosD m' ev') (t' : R) ∧ t' * (Matrix.GeneralLinearGroup.det Pm) ^ 2 = t * ∏ j ∈ Finset.range (g + 1), (Matrix.GeneralLinearGroup.det (B j)) ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)) := by sorry

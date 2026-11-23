-- Prove2me | Theorems.Thm_GlobalTheory_T_degenerationData_torsion_structure_algClosed
-- name    : GlobalTheory.T.degenerationData_torsion_structure_algClosed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:31.141804+00:00
-- url     : https://prove2.me/theorems/1a35a202-4dec-4517-8240-0364db8de3cd
-- title:
--   T: degeneration Data torsion structure alg Closed
-- statement:
--   The T construction uses the degeneration Data torsion structure alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.degenerationData_torsion_structure_algClosed : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (n g : ℕ), (n : C) ≠ 0 → N.Tors n g → ∀ j : ℕ, (∀ b : N.A, ∃ γ : N.Gt, γ.b = b) ∧ (∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n ^ j = γ) ∧ (∀ y : N.X, ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) ∧ Nonempty ((powMonoidHom (n ^ j) : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin (2 * g + Module.finrank ℤ N.X) → ZMod (n ^ j))) ∧ (∀ p : N.QT (n ^ j), (∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1) ↔ ∃ p₀ : N.QT (n ^ j), N.QEq p p₀ ∧ p₀.1.1 = 1 ∧ p₀.1.2.b = 1) ∧ ∀ p : N.QT (n ^ j), (∀ p', N.wp p p' = 1) → N.QEq p 1 := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_T_conjugates_separable_matrix_compact_mod_centralizer
-- name    : GlobalTheory.T.conjugates_separable_matrix_compact_mod_centralizer
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:31.802351+00:00
-- url     : https://prove2.me/theorems/47106b9d-0df0-4a2e-8936-c05d2a28df29
-- title:
--   T: conjugates separable matrix compact mod centralizer
-- statement:
--   The T construction uses the conjugates separable matrix compact mod centralizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.conjugates_separable_matrix_compact_mod_centralizer : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ (A₀ : Matrix (Fin r) (Fin r) F), A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) F), IsCompact Z → ∃ C : Set (GL (Fin r) F), IsCompact C ∧ ∀ g : GL (Fin r) F, (g : Matrix (Fin r) (Fin r) F) * A₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ Z → ∃ c ∈ C, ∃ t : GL (Fin r) F, (t : Matrix (Fin r) (Fin r) F) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) F) ∧ g = c * t) ∧ ∀ (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ C : Set (Matrix.unitaryGroup (Fin r) E), IsCompact C ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * A₀ * star g.1 ∈ Z → ∃ c ∈ C, ∃ t : Matrix.unitaryGroup (Fin r) E, t.1 * A₀ = A₀ * t.1 ∧ g = c * t := by sorry

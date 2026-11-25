-- Prove2me | Theorems.Thm_GlobalTheory_T_alternatingDifference_term_window
-- name    : GlobalTheory.T.alternatingDifference_term_window
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:55.129094+00:00
-- url     : https://prove2.me/theorems/c1f0e159-6160-4b1b-897b-ac7e83914e69
-- title:
--   T: alternating Difference term window
-- statement:
--   The T construction uses the alternating Difference term window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindowStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindowStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.alternatingDifference_term_window : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ I I' : Finset ι, I ⊆ S → I' ⊆ S → (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N : ℕ) (x s : B.A), IsUnit x → IsUnit s → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ k : ℕ, L ≤ k → ∀ (M : Submodule K.O B.A) (p : ι → ℤ), Pos B a e N M p → (term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M ≠ 0 → Win I I' L k p) ∧ (Win I I' L k p → Mid S L k p → term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M = term B π I I' (eS B e I * (x * algebraMap K.O B.A a ^ (2 * k))) (eS B e I' * s) M) := by sorry

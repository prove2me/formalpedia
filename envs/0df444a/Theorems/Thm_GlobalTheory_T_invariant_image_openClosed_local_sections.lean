-- Prove2me | Theorems.Thm_GlobalTheory_T_invariant_image_openClosed_local_sections
-- name    : GlobalTheory.T.invariant_image_openClosed_local_sections
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:01.688263+00:00
-- url     : https://prove2.me/theorems/dbd7449e-900e-4d33-b298-ea4fb1606088
-- title:
--   T: invariant image open Closed local sections
-- statement:
--   The T construction uses the invariant image open Closed local sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantImageOpenClosedLocalSectionsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantImageOpenClosedLocalSectionsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSections
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
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

theorem GlobalTheory.T.invariant_image_openClosed_local_sections : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by sorry

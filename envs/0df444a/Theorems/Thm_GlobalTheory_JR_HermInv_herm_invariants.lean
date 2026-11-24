-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_herm_invariants
-- name    : GlobalTheory.JR.HermInv.herm_invariants
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:16.334524+00:00
-- url     : https://prove2.me/theorems/c5c35f1f-19e2-49cf-b168-3e82edee51fa
-- title:
--   Herm Inv: herm invariants
-- statement:
--   The Herm Inv construction uses the herm invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L477-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L477-L480

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.HermInv.herm_invariants : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ X : Hn r F E, ∃ a : Inv r F, HasInv X a) ∧ (∀ (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F), HasInv X a → HasInv (actU g X) a) ∧ (∀ (X₁ X₂ : Hn r F E) (a : Inv r F), Delta a ≠ 0 → HasInv X₁ a → HasInv X₂ a → ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂) ∧ ∀ a : Inv r F, Delta a ≠ 0 → ((∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E)) := by sorry

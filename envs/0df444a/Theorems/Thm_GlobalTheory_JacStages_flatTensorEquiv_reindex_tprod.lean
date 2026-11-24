-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_flatTensorEquiv_reindex_tprod
-- name    : GlobalTheory.JacStages.flatTensorEquiv_reindex_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:25.252255+00:00
-- url     : https://prove2.me/theorems/0f3ad639-337d-4eef-9ea0-83923aab2a48
-- title:
--   Jac Stages: flat Tensor Equiv reindex tprod
-- statement:
--   The Jac Stages construction uses the flat Tensor Equiv reindex tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean#L89-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
open PiTensorProduct Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.JacStages
variable {s : ℕ} {t : Fin s → ℕ}

theorem GlobalTheory.JacStages.flatTensorEquiv_reindex_tprod (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv (tprod ℂ x)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by sorry

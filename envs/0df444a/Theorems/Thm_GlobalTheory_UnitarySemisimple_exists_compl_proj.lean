-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySemisimple_exists_compl_proj
-- name    : GlobalTheory.UnitarySemisimple.exists_compl_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:31.756793+00:00
-- url     : https://prove2.me/theorems/c2ad0d83-ea98-43da-b322-6d79c50ec6f2
-- title:
--   Unitary Semisimple: exists compl proj
-- statement:
--   The Unitary Semisimple construction uses the exists compl proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIrreducibleSubrepFixedOfUnitary.lean#L34-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIrreducibleSubrepFixedOfUnitary.lean#L34-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.UnitarySemisimple.exists_compl_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) (v : W) :
    ∃ t ∈ Z.toSubmodule, ∀ z ∈ Z.toSubmodule, B z (v - t) = 0 := by sorry

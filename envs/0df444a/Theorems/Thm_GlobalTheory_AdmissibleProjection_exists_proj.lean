-- Prove2me | Theorems.Thm_GlobalTheory_AdmissibleProjection_exists_proj
-- name    : GlobalTheory.AdmissibleProjection.exists_proj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:55:19.93581+00:00
-- url     : https://prove2.me/theorems/112f31d0-5c58-4188-ad6d-a32fdf3aa3bd
-- title:
--   Admissible Projection: exists proj
-- statement:
--   The Admissible Projection construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducibleEquivariantProjection.lean#L58-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducibleEquivariantProjection.lean#L58-L89

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducibleEquivariantProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdmissibleProjection
open GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.AdmissibleProjection.exists_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) :
    ∃ P : W →ₗ[ℂ] W, (∀ w, P w ∈ Z.toSubmodule) ∧ (∀ w, ∀ z ∈ Z.toSubmodule, B z (w - P w) = 0) ∧
      ∀ g w, P (ρ g w) = ρ g (P w) := by sorry

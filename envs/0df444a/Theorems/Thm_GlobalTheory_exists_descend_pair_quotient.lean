-- Prove2me | Theorems.Thm_GlobalTheory_exists_descend_pair_quotient
-- name    : GlobalTheory.exists_descend_pair_quotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:11.773852+00:00
-- url     : https://prove2.me/theorems/5ed5f78a-1ad4-4b58-83dc-38cdc7e9f5db
-- title:
--   Global Theory: exists descend pair quotient
-- statement:
--   The Global Theory construction uses the exists descend pair quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocycle.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocycle.lean#L9-L20

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumInvEqZeroOfUnramifiedCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory

theorem GlobalTheory.exists_descend_pair_quotient {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [TopologicalSpace M] (N : Subgroup Γ) (w : Γ × Γ → M)
    (hw : Continuous w) (h : ∀ g h : Γ, ∀ n ∈ N, ∀ n' ∈ N, w (g * n, h * n') = w (g, h)) :
    ∃ W : (Γ ⧸ N) × (Γ ⧸ N) → M, Continuous W ∧
      ∀ g h : Γ, W ((g : Γ ⧸ N), (h : Γ ⧸ N)) = w (g, h) := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_openSubgroup_units_tateTrivial
-- name    : GroundTheory.LocalField.exists_openSubgroup_units_tateTrivial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:14:36.640116+00:00
-- url     : https://prove2.me/theorems/78277748-9ab4-4708-8fb9-d8652469d62b
-- title:
--   Local Field: exists open Subgroup units tate Trivial
-- statement:
--   The Local Field construction uses the exists open Subgroup units tate Trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L469-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L469-L485

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
open scoped Pointwise

theorem GroundTheory.LocalField.exists_openSubgroup_units_tateTrivial :
    ∃ (π : 𝒪[K]) (θ : L) (k : ℕ), Irreducible π ∧ (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧
      Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ ∧
      (∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) ∧
      ∃ (V : Subgroup 𝒪[L]ˣ)
        (hV : ∀ σ : Gal(L/K), ∀ u ∈ V, ∃ w ∈ V, ((w : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L)),
        (∀ u : 𝒪[L]ˣ, u ∈ V ↔
          ((u : 𝒪[L]) : L) - 1 ∈ π ^ k • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ)) ∧
        IsOpen (V : Set 𝒪[L]ˣ) ∧
        (letI := stableUnitsAction V hV;
          Subsingleton (TateZero Gal(L/K) V) ∧ Subsingleton (TateNegOne Gal(L/K) V)) := by sorry

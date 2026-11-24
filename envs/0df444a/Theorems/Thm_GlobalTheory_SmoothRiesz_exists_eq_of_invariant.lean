-- Prove2me | Theorems.Thm_GlobalTheory_SmoothRiesz_exists_eq_of_invariant
-- name    : GlobalTheory.SmoothRiesz.exists_eq_of_invariant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:29.246351+00:00
-- url     : https://prove2.me/theorems/d1f4a9bf-3f6a-4a08-8250-85af7d196b90
-- title:
--   Smooth Riesz: exists eq of invariant
-- statement:
--   The Smooth Riesz construction uses the exists eq of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryAdmissibleMatrixCoefficient.lean#L38-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryAdmissibleMatrixCoefficient.lean#L38-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.SmoothRiesz

theorem GlobalTheory.SmoothRiesz.exists_eq_of_invariant {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hadm : IsAdmissible σ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hinv : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (L : V →ₗ⋆[ℂ] ℂ)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hL : ∀ s ∈ K, ∀ w, L (σ s w) = L w) : ∃ u : V, ∀ w, L w = Bf u w := by sorry

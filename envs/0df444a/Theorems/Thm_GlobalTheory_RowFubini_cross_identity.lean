-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_cross_identity
-- name    : GlobalTheory.RowFubini.cross_identity
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:40.819709+00:00
-- url     : https://prove2.me/theorems/61aeac0c-7daf-4ae1-a04c-2fb48f6decf0
-- title:
--   Row Fubini: cross identity
-- statement:
--   The Row Fubini construction uses the cross identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L157-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L157-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini

theorem GlobalTheory.RowFubini.cross_identity {X Y : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N : Subgroup X) (π : R →* Y) (σ : Y →* R)
    (hR : IsClosed (R : Set X)) (hN : IsClosed (N : Set X)) (hNR : N ≤ R)
    (hπ : Continuous π) (hσ : Continuous σ) (hsec : ∀ y, π (σ y) = y)
    (hker : ∀ r : R, π r = 1 ↔ r.1 ∈ N)
    (ρ : Measure R) [ρ.IsMulLeftInvariant] (la : Measure N) [la.IsMulLeftInvariant]
    (ν : Measure Y) [ν.IsMulLeftInvariant] (Q₁ Q₂ : Subgroup X) (h12 : Q₁ ≤ Q₂)
    (h1o : IsOpen (Q₁ : Set X)) (h1c : IsCompact (Q₁ : Set X))
    (h2o : IsOpen (Q₂ : Set X)) (h2c : IsCompact (Q₂ : Set X)) :
    ρ.real (Q₂.comap R.subtype) * la.real (Q₁.comap N.subtype) *
        ν.real ((Q₁.comap R.subtype).map π) =
      ρ.real (Q₁.comap R.subtype) * la.real (Q₂.comap N.subtype) *
        ν.real ((Q₂.comap R.subtype).map π) := by sorry

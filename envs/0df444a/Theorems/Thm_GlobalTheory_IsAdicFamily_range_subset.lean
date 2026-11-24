-- Prove2me | Theorems.Thm_GlobalTheory_IsAdicFamily_range_subset
-- name    : GlobalTheory.IsAdicFamily.range_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:44.31212+00:00
-- url     : https://prove2.me/theorems/6eae8846-9686-447d-87bb-b8cdbbcb4d1d
-- title:
--   Is Adic Family: range subset
-- statement:
--   The Is Adic Family construction uses the range subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L265-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L265-L270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]

theorem GlobalTheory.IsAdicFamily.range_subset (hI : I ≠ ⊤) {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) {U : X.Opens}
    (hU : haveI := isLocalRing_quotient_pow hI 0; f 0 (closedPoint (R ⧸ I ^ (0 + 1))) ∈ U)
    (n : ℕ) : Set.range (f n) ⊆ U := by sorry

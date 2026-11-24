-- Prove2me | Theorems.Thm_GlobalTheory_Pat_isCplAt_approx
-- name    : GlobalTheory.Pat.isCplAt_approx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:48.91879+00:00
-- url     : https://prove2.me/theorems/f6af6d39-3bc5-4479-b85f-5b7f078f579e
-- title:
--   Pat: is Cpl At approx
-- statement:
--   The Pat construction uses the is Cpl At approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCplAtApprox.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCplAtApprox.lean#L83-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat

theorem GlobalTheory.Pat.isCplAt_approx : ∀ (R S : Type) [CommRing R] [CommRing S] [IsLocalRing S] (q : Ideal R)
    [q.IsPrime] (φ : R →+* S), IsCplAt q φ → ∀ k : ℕ,
    (∀ s : S, ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k) ∧
      ∀ a : R, φ a ∈ maximalIdeal S ^ k → ∃ b ∉ q, b * a ∈ q ^ k := by sorry

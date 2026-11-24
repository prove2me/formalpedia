-- Prove2me | Theorems.Thm_GlobalTheory_Pat_IsCplAt_approx_inj
-- name    : GlobalTheory.Pat.IsCplAt.approx_inj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:01.067568+00:00
-- url     : https://prove2.me/theorems/e36f84d8-eedb-4455-a684-8c45c8b8f93e
-- title:
--   Is Cpl At: approx inj
-- statement:
--   The Is Cpl At construction uses the approx inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCplAtApprox.lean#L53-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCplAtApprox.lean#L53-L81

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

theorem GlobalTheory.Pat.IsCplAt.approx_inj {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (a : R)
    (ha : φ a ∈ maximalIdeal S ^ k) : ∃ b ∉ q, b * a ∈ q ^ k := by sorry

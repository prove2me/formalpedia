-- Prove2me | Theorems.Thm_GlobalTheory_Pat_IsCplAt_approx_surj
-- name    : GlobalTheory.Pat.IsCplAt.approx_surj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:41:39.276516+00:00
-- url     : https://prove2.me/theorems/e4daaa4a-194b-4b07-a592-96e1bcb884b3
-- title:
--   Is Cpl At: approx surj
-- statement:
--   The Is Cpl At construction uses the approx surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCplAtApprox.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCplAtApprox.lean#L39-L51

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

theorem GlobalTheory.Pat.IsCplAt.approx_surj {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (s : S) :
    ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k := by sorry

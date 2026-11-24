-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_exists_derivation_lift
-- name    : GlobalTheory.HenselZero.exists_derivation_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:01.756832+00:00
-- url     : https://prove2.me/theorems/46241f67-dd03-4995-bd1d-af57f21432af
-- title:
--   Hensel Zero: exists derivation lift
-- statement:
--   The Hensel Zero construction uses the exists derivation lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FormallySmoothQuotient.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FormallySmoothQuotient.lean#L41-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
open IsLocalRing GlobalTheory.SqZero

theorem GlobalTheory.HenselZero.exists_derivation_lift {R S K : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [CommRing K] [Algebra R K] (u : S →ₐ[R] K) (hu : Function.Surjective u) (D : S →ₗ[R] K)
    (hD : ∀ a b, D (a * b) = u a * D b + u b * D a) : ∃ τ : Derivation R S S, ∀ a, u (τ a) = D a := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_isLocalizationAway_subring
-- name    : GlobalTheory.QcSub.isLocalizationAway_subring
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:03:42.743883+00:00
-- url     : https://prove2.me/theorems/f5141e48-a61e-496c-bd96-45d42126fb38
-- title:
--   Qc Sub: is Localization Away subring
-- statement:
--   The Qc Sub construction uses the is Localization Away subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoequifiberedGeneratedSubalgebraQuasiCoherent.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoequifiberedGeneratedSubalgebraQuasiCoherent.lean#L7-L28

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoequifiberedGeneratedSubalgebraQuasiCoherent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
open GlobalTheory GlobalTheory.QcSub

theorem GlobalTheory.QcSub.isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    letI := (ρ.restrict S S' hρ).toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : S) S' := by sorry

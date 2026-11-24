-- Prove2me | Theorems.Thm_GlobalTheory_DualFormOrtho_bilin_eq_zero_of_span
-- name    : GlobalTheory.DualFormOrtho.bilin_eq_zero_of_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:52:03.5284+00:00
-- url     : https://prove2.me/theorems/2166ae78-5910-4e8a-bcf6-e1b03ff84e38
-- title:
--   Dual Form Ortho: bilin eq zero of span
-- statement:
--   The Dual Form Ortho construction uses the bilin eq zero of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormValueOfValues.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormValueOfValues.lean#L10-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormValueOfValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DualFormOrtho

theorem GlobalTheory.DualFormOrtho.bilin_eq_zero_of_span {V : Type} [AddCommGroup V] [Module ℂ V] (B : LinearMap.BilinForm ℂ V) {s t : Set V}
    (h : ∀ u ∈ s, ∀ v ∈ t, B u v = 0) {a b : V} (ha : a ∈ Submodule.span ℂ s) (hb : b ∈ Submodule.span ℂ t) : B a b = 0 := by sorry

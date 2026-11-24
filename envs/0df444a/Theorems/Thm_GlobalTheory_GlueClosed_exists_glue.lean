-- Prove2me | Theorems.Thm_GlobalTheory_GlueClosed_exists_glue
-- name    : GlobalTheory.GlueClosed.exists_glue
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:55:14.395293+00:00
-- url     : https://prove2.me/theorems/cbe64b26-d170-4da8-aead-edb29a45ac72
-- title:
--   Glue Closed: exists glue
-- statement:
--   The Glue Closed construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueClosedImmersionsOpenCover.lean#L51-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueClosedImmersionsOpenCover.lean#L51-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueClosedImmersionsOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GlueClosed

theorem GlobalTheory.GlueClosed.exists_glue {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)
    (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) (C : S → Scheme.{0}) (c : ∀ U, C U ⟶ U.1.toScheme)
    [∀ U, Mono (c U)]
    (H : ∀ (U V : S) (h : U.1 ≤ V.1) (Y : Scheme.{0}) (g : Y ⟶ U.1.toScheme),
      (∃ z : Y ⟶ C U, z ≫ c U = g) ↔ ∃ z : Y ⟶ C V, z ≫ c V = g ≫ X.homOfLE h) :
    ∃ (B : Scheme.{0}) (b : B ⟶ X) (e : ∀ U, C U ⟶ B), ∀ U, IsPullback (c U) (e U) U.1.ι b := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_isPullback_of_charts
-- name    : GlobalTheory.AffineQuotient.isPullback_of_charts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:54:43.966251+00:00
-- url     : https://prove2.me/theorems/1ec271d9-1631-4162-8d0c-c6b36a154cfb
-- title:
--   Affine Quotient: is Pullback of charts
-- statement:
--   The Affine Quotient construction uses the is Pullback of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L224-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L224-L232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]

theorem GlobalTheory.AffineQuotient.isPullback_of_charts {Z Q : Scheme.{0}} (b : W ⟶ Z) (q : X ⟶ Q) (q' : Z ⟶ Q) {ι : Type}
    (W' X' : ι → Scheme.{0}) (u : ∀ i, W' i ⟶ W) (v : ∀ i, X' i ⟶ X) (a' : ∀ i, W' i ⟶ X' i)
    [∀ i, IsOpenImmersion (v i)] (hv : ∀ y, ∃ i z, v i z = y)
    (h : ∀ i, IsPullback (a' i) (u i) (v i) a)
    (h' : ∀ i, IsPullback (a' i) (u i ≫ b) (v i ≫ q) q') : IsPullback a b q q' := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_isPullback_toQuot
-- name    : GlobalTheory.AffineQuotient.isPullback_toQuot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:54:51.241802+00:00
-- url     : https://prove2.me/theorems/b6f9b44b-537c-480d-80ca-f9fc8a5c528c
-- title:
--   Affine Quotient: is Pullback to Quot
-- statement:
--   The Affine Quotient construction uses the is Pullback to Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L255-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L255-L260

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

theorem GlobalTheory.AffineQuotient.isPullback_toQuot (U : Y.affineOpens) (hf : IsAffineOpen (f ⁻¹ᵁ U.1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)) hf.fromSpec
      ((cover f g a ha p hp).f U) (toQuot f g a ha p hp) := by sorry

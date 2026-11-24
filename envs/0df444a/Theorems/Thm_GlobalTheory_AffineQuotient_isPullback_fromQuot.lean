-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_isPullback_fromQuot
-- name    : GlobalTheory.AffineQuotient.isPullback_fromQuot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:54:41.316638+00:00
-- url     : https://prove2.me/theorems/9f2d2d75-6ac2-49ad-8128-021e107051c3
-- title:
--   Affine Quotient: is Pullback from Quot
-- statement:
--   The Affine Quotient construction uses the is Pullback from Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L262-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L262-L266

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

theorem GlobalTheory.AffineQuotient.isPullback_fromQuot (U : Y.affineOpens) :
    IsPullback (Spec.map ((diagramMap f g a ha p hp).app (.op U.1))) ((cover f g a ha p hp).f U)
      U.2.fromSpec (fromQuot f g a ha p hp) := by sorry

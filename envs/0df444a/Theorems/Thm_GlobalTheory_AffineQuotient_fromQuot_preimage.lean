-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_fromQuot_preimage
-- name    : GlobalTheory.AffineQuotient.fromQuot_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:51.859103+00:00
-- url     : https://prove2.me/theorems/77e22c65-10c2-4771-a58a-1483b2039691
-- title:
--   Affine Quotient: from Quot preimage
-- statement:
--   The Affine Quotient construction uses the from Quot preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L194-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L194-L196

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
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalTheory.AffineQuotient.fromQuot_preimage (U : Y.affineOpens) :
    fromQuot f g a ha p hp ⁻¹ᵁ U = ((cover f g a ha p hp).f U).opensRange := by sorry

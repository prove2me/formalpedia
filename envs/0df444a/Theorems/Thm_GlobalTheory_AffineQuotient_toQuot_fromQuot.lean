-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_toQuot_fromQuot
-- name    : GlobalTheory.AffineQuotient.toQuot_fromQuot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:15.286351+00:00
-- url     : https://prove2.me/theorems/3fb55d8a-d72e-4b77-9f62-6515bedcbaec
-- title:
--   Affine Quotient: to Quot from Quot
-- statement:
--   The Affine Quotient construction uses the to Quot from Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L200-L206

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

theorem GlobalTheory.AffineQuotient.toQuot_fromQuot : toQuot f g a ha p hp ≫ fromQuot f g a ha p hp = f := by sorry

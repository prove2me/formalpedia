-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_exists_fromSpec_eq
-- name    : GlobalTheory.AffineQuotient.exists_fromSpec_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:58.208229+00:00
-- url     : https://prove2.me/theorems/1eb2aa94-43b3-4871-8216-d3e67ef330ec
-- title:
--   Affine Quotient: exists from Spec eq
-- statement:
--   The Affine Quotient construction uses the exists from Spec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L269-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L269-L276

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

theorem GlobalTheory.AffineQuotient.exists_fromSpec_eq [IsAffineHom f] (x : X) :
    ∃ (U : Y.affineOpens) (z : Spec Γ(X, f ⁻¹ᵁ U.1)), (U.2.preimage f).fromSpec z = x := by sorry

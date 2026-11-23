-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_SpecMap_pullOver
-- name    : GlobalTheory.AffineQuotient.SpecMap_pullOver
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:14.499114+00:00
-- url     : https://prove2.me/theorems/59eaa4a0-2efc-4d45-8056-7f2f1b2ff336
-- title:
--   Affine Quotient: Spec Map pull Over
-- statement:
--   The Affine Quotient construction uses the Spec Map pull Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L235-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L235-L237

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

theorem GlobalTheory.AffineQuotient.SpecMap_pullOver {U : Y.Opens} (hf : IsAffineOpen (f ⁻¹ᵁ U)) (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    Spec.map (pullOver f g a ha U) ≫ hf.fromSpec = hg.fromSpec ≫ a := by sorry

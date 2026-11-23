-- Prove2me | Theorems.Thm_GlobalTheory_PartialCocycle_gm_iso
-- name    : GlobalTheory.PartialCocycle.gm_iso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:08.506802+00:00
-- url     : https://prove2.me/theorems/a0c4aafa-a1d2-415c-bda5-c38e734cf16f
-- title:
--   Partial Cocycle: gm iso
-- statement:
--   The Partial Cocycle construction uses the gm iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RigidifiedPartialLineBundleIsoCocycle.lean#L30-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RigidifiedPartialLineBundleIsoCocycle.lean#L30-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.PartialCocycle

theorem GlobalTheory.PartialCocycle.gm_iso {X Z : Scheme.{0}} {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen) (f : Z ⟶ X) (z : Z)
    (a a' : M.ι) (b b' : L.ι) (ha : f z ∈ M.U a) (ha' : f z ∈ M.U a') (hb : f z ∈ L.U b) (hb' : f z ∈ L.U b') :
    gm f z (M.U a ⊓ L.U b) (w.s (a, b)) =
      gm f z (M.U a ⊓ M.U a') (M.g a a') * (gm f z (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
        gm f z (M.U a' ⊓ L.U b') (w.s (a', b')) := by sorry

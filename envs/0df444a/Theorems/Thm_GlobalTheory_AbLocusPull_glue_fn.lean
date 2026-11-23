-- Prove2me | Theorems.Thm_GlobalTheory_AbLocusPull_glue_fn
-- name    : GlobalTheory.AbLocusPull.glue_fn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:49.564804+00:00
-- url     : https://prove2.me/theorems/76819d87-003e-4c54-a172-2dc2277150eb
-- title:
--   Ab Locus Pull: glue fn
-- statement:
--   The Ab Locus Pull construction uses the glue fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProperRestrictPull.lean#L28-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProperRestrictPull.lean#L28-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.AbLocusPull.glue_fn {κ : Type} (V : X.Opens) (O : κ → X.Opens) (hO : ∀ k, O k ≤ V)
    (hc : ∀ x ∈ V, ∃ k, x ∈ O k) (a : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l → gs (𝟙 X) x (O k) (a k) = gs (𝟙 X) x (O l) (a l)) :
    ∃ b : Γ(X, V), ∀ x k, x ∈ O k → gs (𝟙 X) x V b = gs (𝟙 X) x (O k) (a k) := by sorry

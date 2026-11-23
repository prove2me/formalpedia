-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_MulN_surjective_of_geomFibres
-- name    : GlobalTheory.AbLaw.MulN.surjective_of_geomFibres
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:55.314847+00:00
-- url     : https://prove2.me/theorems/40445d71-ebec-4eca-9499-bbacbceb7e09
-- title:
--   Mul N: surjective of geom Fibres
-- statement:
--   The Mul N construction uses the surjective of geom Fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MulAFiniteFlatSurjectiveEtale.lean#L36-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MulAFiniteFlatSurjectiveEtale.lean#L36-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.MulN

theorem GlobalTheory.AbLaw.MulN.surjective_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Surjective ((Over.pullback t).map f).left) : Surjective f.left := by sorry

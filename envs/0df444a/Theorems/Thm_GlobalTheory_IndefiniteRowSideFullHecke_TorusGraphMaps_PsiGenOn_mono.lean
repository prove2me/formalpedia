-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TorusGraphMaps_PsiGenOn_mono
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps.PsiGenOn.mono
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:44.327363+00:00
-- url     : https://prove2.me/theorems/988648ab-f68b-47f5-8f2a-3a84dd7cad86
-- title:
--   Psi Gen On: mono
-- statement:
--   The Psi Gen On construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TorusGraphMaps.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TorusGraphMaps.lean#L56-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps.PsiGenOn.mono {D : DegPre R} {χ : D.X} {U U' : Set (Spec (CommRingCat.of R))}
    (h : PsiGenOn D χ U) (hU : U' ⊆ U) : PsiGenOn D χ U' := by sorry

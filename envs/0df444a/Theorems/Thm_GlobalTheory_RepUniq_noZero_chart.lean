-- Prove2me | Theorems.Thm_GlobalTheory_RepUniq_noZero_chart
-- name    : GlobalTheory.RepUniq.noZero_chart
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:53.922557+00:00
-- url     : https://prove2.me/theorems/bd8eba53-8158-4469-8925-ebaf6cec4e7b
-- title:
--   Rep Uniq: no Zero chart
-- statement:
--   The Rep Uniq construction uses the no Zero chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L315-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L315-L324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}
variable {R : Type} [CommRing R] {I I' : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R}

theorem GlobalTheory.RepUniq.noZero_chart (h : ProjRep I s M th) (k : M.ι) : NoZero fun i => (th i).f k := by sorry

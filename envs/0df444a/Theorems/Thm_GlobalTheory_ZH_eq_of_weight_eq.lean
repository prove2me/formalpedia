-- Prove2me | Theorems.Thm_GlobalTheory_ZH_eq_of_weight_eq
-- name    : GlobalTheory.ZH.eq_of_weight_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:30.010036+00:00
-- url     : https://prove2.me/theorems/c9eadf67-0ac0-4dda-9b98-de55e774cf79
-- title:
--   ZH: eq of weight eq
-- statement:
--   The ZH construction uses the eq of weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOfWeightEq.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOfWeightEq.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOfWeightEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ZH

theorem GlobalTheory.ZH.eq_of_weight_eq {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) {s s' : Γ(G.left, D.q.left ⁻¹ᵁ V)}
    (e : ∀ χ, D.weight j V hV h χ s = D.weight j V hV h χ s') : s = s' := by sorry

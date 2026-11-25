-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_eq_idealSheaf
-- name    : GlobalTheory.EffCartierData.eq_idealSheaf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:20.626426+00:00
-- url     : https://prove2.me/theorems/d007dd93-248e-4331-a76a-b00fafcb458f
-- title:
--   Eff Cartier Data: eq ideal Sheaf
-- statement:
--   The Eff Cartier Data construction uses the eq ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L245-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L245-L251

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
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
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)

theorem GlobalTheory.EffCartierData.eq_idealSheaf {I : X.IdealSheafData}
    (h : ∀ x : X, ∃ (W : X.affineOpens) (i : D.ι) (hW : W.1 ≤ D.U i),
      x ∈ W.1 ∧ I.ideal W = Ideal.span {resG X hW (D.f i)}) : I = D.idealSheaf := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_mem_idealSheaf_iff
-- name    : GlobalTheory.EffCartierData.mem_idealSheaf_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:21:00.022392+00:00
-- url     : https://prove2.me/theorems/2c7e8d9b-3abe-5ef9-9a8b-579570987d10
-- title:
--   Eff Cartier Data: mem ideal Sheaf iff
-- statement:
--   The Eff Cartier Data construction uses the mem ideal Sheaf iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L222-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L222-L231

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

theorem GlobalTheory.EffCartierData.mem_idealSheaf_iff {W : X.affineOpens} {a : Γ(X, W.1)} :
    a ∈ D.idealSheaf.ideal W ↔ ∀ i, resG X (inf_le_right : W.1 ⊓ D.U i ≤ D.U i) (D.f i) ∣
      resG X (inf_le_left : W.1 ⊓ D.U i ≤ W.1) a := by sorry

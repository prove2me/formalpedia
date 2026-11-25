-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_germK_eq_pow_mul_ratOf
-- name    : GlobalTheory.EffCartierData.germK_eq_pow_mul_ratOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:40.150693+00:00
-- url     : https://prove2.me/theorems/20257355-7a63-4db1-84af-9e9b6bf186bc
-- title:
--   Eff Cartier Data: germ K eq pow mul rat Of
-- statement:
--   The Eff Cartier Data construction uses the germ K eq pow mul rat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L751-L759
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L751-L759

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
variable [IsIntegral X]

theorem GlobalTheory.EffCartierData.germK_eq_pow_mul_ratOf (n : ℕ) (V : X.Opens) [Nonempty V]
    {t : ∀ i, Γ(X, V ⊓ (D.nsmul n).lb.U i)} (ht : t ∈ secOn (D.nsmul n).lb V) (i : D.ι)
    [hi : Nonempty (V ⊓ D.U i : X.Opens)] :
    (X.germToFunctionField (V ⊓ D.U i)).hom (t i) =
      (X.germToFunctionField (V ⊓ D.U i)).hom (resG X inf_le_right (D.f i)) ^ n *
        ratOf (D.nsmul n).isLB_lb (D.nsmul n).canonical V t := by sorry

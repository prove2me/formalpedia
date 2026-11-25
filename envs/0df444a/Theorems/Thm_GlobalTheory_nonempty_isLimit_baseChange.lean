-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_isLimit_baseChange
-- name    : GlobalTheory.nonempty_isLimit_baseChange
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:42.773658+00:00
-- url     : https://prove2.me/theorems/4bbd019a-e2ad-5bf7-9900-0c84ce6db953
-- title:
--   Global Theory: nonempty is Limit base Change
-- statement:
--   The Global Theory construction uses the nonempty is Limit base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L402-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L402-L446

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)

theorem GlobalTheory.nonempty_isLimit_baseChange (h : R₀.FG) :
    Nonempty (IsLimit (schemeConeOfFamily (baseChangeDiagram R₀ pB)
      (X := pullback pB (spMap (algebraMap k C))) (fun R => baseChangeMap pB R.unop.1.val)
      (fun {R T} f => baseChangeMap_comp pB
        (Subalgebra.inclusion (show T.unop.1 ≤ R.unop.1 from leOfHom f.unop)) R.unop.1.val))) := by sorry

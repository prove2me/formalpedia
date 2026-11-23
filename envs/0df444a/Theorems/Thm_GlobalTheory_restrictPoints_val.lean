-- Prove2me | Theorems.Thm_GlobalTheory_restrictPoints_val
-- name    : GlobalTheory.restrictPoints_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:12.408118+00:00
-- url     : https://prove2.me/theorems/9070336d-c5a5-4de3-92cb-b1e9def101ef
-- title:
--   Global Theory: restrict Points val
-- statement:
--   The Global Theory construction uses the restrict Points val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L343-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L343-L344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory

theorem GlobalTheory.restrictPoints_val {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S) (i : T₀ ⟶ T)
    (l : {l : T ⟶ X // l ≫ f = h}) : (restrictPoints f h i l).1 = i ≫ l.1 := by sorry

attribute [defeq] GlobalTheory.restrictPoints_val

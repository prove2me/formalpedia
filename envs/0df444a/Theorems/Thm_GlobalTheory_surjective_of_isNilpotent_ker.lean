-- Prove2me | Theorems.Thm_GlobalTheory_surjective_of_isNilpotent_ker
-- name    : GlobalTheory.surjective_of_isNilpotent_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:26.225797+00:00
-- url     : https://prove2.me/theorems/d0a28df0-1961-42f9-a1d9-d3a6fb451941
-- title:
--   Global Theory: surjective of is Nilpotent ker
-- statement:
--   The Global Theory construction uses the surjective of is Nilpotent ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L128-L135

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

theorem GlobalTheory.surjective_of_isNilpotent_ker {T₀ T : Scheme.{u}} (i : T₀ ⟶ T) [IsClosedImmersion i]
    (hi : IsNilpotent i.ker) : Surjective i := by sorry

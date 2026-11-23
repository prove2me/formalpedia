-- Prove2me | Theorems.Thm_GaussValuationUniqueness_sac_succAbove
-- name    : GaussValuationUniqueness.sac_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:44.580418+00:00
-- url     : https://prove2.me/theorems/64aa0219-8a72-4086-ae1a-18d86a941bee
-- title:
--   Gauss Valuation Uniqueness: sac succ Above
-- statement:
--   The Gauss Valuation Uniqueness construction uses the sac succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L64-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0

theorem GaussValuationUniqueness.sac_succAbove {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α)
    (k : Fin n) : Fin.succAboveCases (α := fun _ => α) i x f (i.succAbove k) = f k := by sorry

-- Prove2me | Theorems.Thm_MorreySubadditive
-- name    : MorreySubadditive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:31.57794+00:00
-- url     : https://prove2.me/theorems/4e1858a8-1230-4912-8e28-156fc8cb6d84
-- title:
--   Morrey Subadditive: Morrey Subadditive
-- statement:
--   The Morrey Subadditive construction uses the Morrey Subadditive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MorreySubadditive.lean#L6-L25
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MorreySubadditive.lean#L6-L25

import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_MorreySubadditive
set_option autoImplicit false
open MeasureTheory Set

theorem MorreySubadditive {E : Type*} [MetricSpace E] [MeasurableSpace E]
    {ι : Type*} (s : Finset ι) (μ : ι → Measure E) :
    morreyNorm (∑ i ∈ s, μ i) ≤ ∑ i ∈ s, morreyNorm (μ i) := by sorry

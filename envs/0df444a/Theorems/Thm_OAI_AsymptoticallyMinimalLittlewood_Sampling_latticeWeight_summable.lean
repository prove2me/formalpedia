-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_latticeWeight_summable
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.latticeWeight_summable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:51:02.720239+00:00
-- url     : https://prove2.me/theorems/fa022d02-4e83-4539-ad93-4866f3e9733b
-- title:
--   Summability of the lattice weight $(1+|w|)^{-2}$ over the integers
-- statement:
--   For an integer $w\in\mathbb{Z}$ define the lattice weight $\omega(w)=(1+|w|)^{-2}$. Then $\omega$ is summable over $\mathbb{Z}$:
--   $$
--   \sum_{w\in\mathbb{Z}}\frac{1}{(1+|w|)^{2}}<\infty .
--   $$
--
--   The weight $\omega$ is the summable majorant used to control the tails of dual sums produced by Poisson summation: a family of oscillatory integrals indexed by $l\in\mathbb{Z}$ whose size is at most a constant times $(1+|l|)^{-2}$ can be summed over all $l$, with total at most that constant times $\sum_{w}\omega(w)$.
--
--   **Formalization Note** The weight is the real-valued function `latticeWeight w = 1/(1+|(w:ℝ)|)^2`, and the statement is `Summable latticeWeight`, Mathlib's unconditional summability of a family indexed by $\mathbb{Z}$; for nonnegative terms this is the same as convergence of the series.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingTail.lean#L17-L28

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.latticeWeight_summable : Summable latticeWeight := by sorry

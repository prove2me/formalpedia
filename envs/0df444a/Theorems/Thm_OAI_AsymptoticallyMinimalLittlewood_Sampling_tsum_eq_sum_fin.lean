-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_tsum_eq_sum_fin
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.tsum_eq_sum_fin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:56:55.611984+00:00
-- url     : https://prove2.me/theorems/27718180-6dd0-42d1-b6fc-7aed79eaafcb
-- title:
--   A series over $\mathbb{Z}$ supported in $\{0,\dots,N-1\}$ equals the finite sum
-- statement:
--   Let $N\ge0$ be an integer and let $f:\mathbb{Z}\to\mathbb{C}$ vanish outside $\{0,1,\dots,N-1\}$, that is, $f(k)=0$ whenever $k<0$ or $k\ge N$. Then
--   $$
--   \sum_{k\in\mathbb{Z}}f(k)=\sum_{k=0}^{N-1}f(k).
--   $$
--
--   This identifies the doubly infinite sums produced by Poisson summation with the finite sums $\sum_{k=0}^{N-1}$ that define the coefficients of a polynomial of degree less than $N$. It is applied to sampled sequences $k\mapsto g(k/N)\,(\cdots)$ whose amplitude $g$ is supported in $(0,1)$.
--
--   **Formalization Note** The left side is Mathlib's `tsum`; since $f$ has finite support it is a genuine finite sum and no summability hypothesis is needed. The right side is indexed by `Fin N`, with $k$ cast to $\mathbb{Z}$. For $N=0$ both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingEnergy.lean#L174-L193

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
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.tsum_eq_sum_fin {N : ℕ} (f : ℤ → ℂ)
    (hf : ∀ k : ℤ, k<0 ∨ (N : ℤ)≤k → f k=0) :
    (∑' k : ℤ, f k)=∑ k : Fin N, f k.val := by sorry

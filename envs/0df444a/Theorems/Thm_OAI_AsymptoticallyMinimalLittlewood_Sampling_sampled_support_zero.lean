-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_sampled_support_zero
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.sampled_support_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:57:34.729712+00:00
-- url     : https://prove2.me/theorems/c4d3947d-8463-45f8-b059-d9a656b2a631
-- title:
--   Samples $g(k/N)$ vanish for $k$ outside $\{0,\dots,N-1\}$ when $g$ is supported in $(0,1)$
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be a function whose closed support $\overline{\{x: g(x)\neq0\}}$ is contained in the open interval $(0,1)$. Let $N\ge1$ be an integer and $k\in\mathbb{Z}$ with $k<0$ or $k\ge N$. Then
--   $$
--   g\Bigl(\frac kN\Bigr)=0 .
--   $$
--
--   Consequently the samples $g(k/N)$, $k\in\mathbb{Z}$, of an amplitude supported in $(0,1)$ can be nonzero only for $0\le k\le N-1$, so a sum over all of $\mathbb{Z}$ of terms containing the factor $g(k/N)$ is a sum of $N$ terms, matching the coefficient range of a polynomial of degree less than $N$.
--
--   **Formalization Note** The support hypothesis is `tsupport g ⊆ Set.Ioo 0 1`; no regularity of $g$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingEnergy.lean#L195-L208

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

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.sampled_support_zero {g : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {N : ℕ} (hN : 0<N) {k : ℤ} (hk : k<0 ∨ (N : ℤ)≤k) :
    g ((k : ℝ)/N)=0 := by sorry

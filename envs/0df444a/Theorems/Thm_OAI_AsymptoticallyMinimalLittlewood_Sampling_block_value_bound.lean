-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_block_value_bound
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.block_value_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:01:04.11172+00:00
-- url     : https://prove2.me/theorems/1a275eef-a15c-4eb1-a24e-2a80c82c4697
-- title:
--   Disjointly supported weights in $[0,1]$ keep a combination of unit-bounded values in the unit disc
-- statement:
--   Let $H\ge0$ be an integer, let $\chi_0,\dots,\chi_{H-1}$ be real numbers with $0\le\chi_h\le1$, and let $F_0,\dots,F_{H-1}$ be complex numbers with $|F_h|\le1$. Suppose that $\chi_h\chi_{h'}=0$ whenever $h\neq h'$, so that at most one $\chi_h$ is nonzero. Then
--   $$
--   \Bigl|\sum_{h=0}^{H-1}\chi_h\,F_h\Bigr|\le1 .
--   $$
--
--   In applications the $\chi_h$ are the values at one point of cutoff functions with pairwise disjoint supports, one for each block, and the $F_h$ are values of functions bounded by $1$; the lemma guarantees that the glued function $\sum_h\chi_hF_h$ still takes values in the closed unit disc. It is used to check that the sampled real sequence assembled from packed chirp blocks stays in $[-1,1]$.
--
--   **Formalization Note** The index runs over `Fin H`, and each $\chi_h$ is cast from $\mathbb{R}$ to $\mathbb{C}$ before multiplying.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BlockSampling.lean#L203-L219

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
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
universe uP uJ uI
open scoped BigOperators ComplexConjugate
open Complex UnitAddTorus
open QuadraticTail

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.block_value_bound {H : ℕ} (χ : Fin H → ℝ) (F : Fin H → ℂ)
    (hχ : ∀ h, 0≤χ h ∧ χ h≤1) (hF : ∀ h, ‖F h‖≤1)
    (hdisj : ∀ i j, i≠j → χ i*χ j=0) :
    ‖∑ h, (χ h : ℂ)*F h‖≤1 := by sorry

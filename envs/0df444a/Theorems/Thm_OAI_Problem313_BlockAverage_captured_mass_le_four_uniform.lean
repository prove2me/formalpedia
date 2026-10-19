-- Prove2me | Theorems.Thm_OAI_Problem313_BlockAverage_captured_mass_le_four_uniform
-- name    : OAI.Problem313.BlockAverage.captured_mass_le_four_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:19:29.896993+00:00
-- url     : https://prove2.me/theorems/a8238077-f0c3-4a84-a794-1b98f38f4a3e
-- title:
--   Low Fourier mass is at most four times the influence bound
-- statement:
--   Let $\Omega$ be a finite set of blocks with the uniform distribution, $w\ge0$ on items, $I\ge0$ on coordinates, $a\ge0$ and $c>0$. Assume:
--
--   1. every item $s\in L$ is captured by a fraction $\ge c$ of the blocks;
--   2. every block $b$ satisfies $\sum_{s:P(b,s)}w_s\le a\sum_{i:E(b,i)}I_i$;
--   3. every coordinate is incident to a fraction $\le4c$ of the blocks.
--
--   Then
--   $$
--   \sum_{s\in L}w_s\le4a\sum_iI_i .
--   $$
--
--   This is the averaging step of the proof: low-degree Fourier mass of the whole function is bounded through restrictions to random vertex blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockAverage.lean#L147-L179

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative

open OAI OAI.Problem313
universe u v w
open scoped BigOperators

theorem OAI.Problem313.BlockAverage.captured_mass_le_four_uniform
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [DecidableEq β] [Fintype ι]
    (Ω : Finset β) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hI : ∀ i, 0 ≤ I i)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤
      ((Ω.filter (fun b => P b s)).card : ℝ) / Ω.card)
    (hblock : ∀ b ∈ Ω, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i,
      ((Ω.filter (fun b => E b i)).card : ℝ) / Ω.card ≤ 4 * c) :
    (∑ s ∈ low, w s) ≤ 4 * a * ∑ i, I i := by sorry

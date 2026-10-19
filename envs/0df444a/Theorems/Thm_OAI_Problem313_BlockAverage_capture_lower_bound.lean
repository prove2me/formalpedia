-- Prove2me | Theorems.Thm_OAI_Problem313_BlockAverage_capture_lower_bound
-- name    : OAI.Problem313.BlockAverage.capture_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:16:08.82097+00:00
-- url     : https://prove2.me/theorems/d2126c02-6460-45ea-9c0b-a07545c08852
-- title:
--   Captured mass is at least the capture probability times the mass
-- statement:
--   Let $\mu\ge0$ be weights on a finite set of blocks $b$, $w\ge0$ weights on items $s$, and $P(b,s)$ the relation "$b$ captures $s$". If every item $s$ in a set $L$ is captured with weight at least $c$, i.e. $\sum_{b:P(b,s)}\mu_b\ge c$, then
--   $$
--   c\sum_{s\in L}w_s\le\sum_b\mu_b\sum_{s:P(b,s)}w_s .
--   $$
--
--   Averaging over random blocks, the captured Fourier mass is at least the capture probability times the low-level mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockAverage.lean#L40-L59

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

theorem OAI.Problem313.BlockAverage.capture_lower_bound
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] (low : Finset α) (c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0) :
    c * ∑ s ∈ low, w s ≤ ∑ b, μ b * ∑ s, if P b s then w s else 0 := by sorry

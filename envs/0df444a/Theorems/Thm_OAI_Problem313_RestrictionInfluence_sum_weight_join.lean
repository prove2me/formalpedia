-- Prove2me | Theorems.Thm_OAI_Problem313_RestrictionInfluence_sum_weight_join
-- name    : OAI.Problem313.RestrictionInfluence.sum_weight_join
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:21:16.703961+00:00
-- url     : https://prove2.me/theorems/ae5a3333-256a-413f-8276-6536730eb189
-- title:
--   Fubini for a free/exterior split of coordinates
-- statement:
--   Let $\iota$ be a finite set of coordinates and $P$ a predicate splitting it into free coordinates $\{i:P(i)\}$ and exterior coordinates $\{i:\neg P(i)\}$. For a free configuration $x$ and an exterior configuration $y$, $\mathrm{join}(x,y)$ is the full configuration. The $p$-biased weight is $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$ on any coordinate set. For every $g:\{0,1\}^\iota\to\mathbb{R}$,
--   $$
--   \sum_zw_p(z)g(z)=\sum_yw_p(y)\sum_xw_p(x)\,g(\mathrm{join}(x,y)) .
--   $$
--
--   Expectations factor through the restriction: first average over the free coordinates with the exterior fixed, then over the exterior.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RestrictionInfluence.lean#L50-L67

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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence

open OAI OAI.Problem313 OAI.Problem313.RestrictionInfluence
universe u
open scoped BigOperators
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (P : ι → Prop) [DecidablePred P]

theorem OAI.Problem313.RestrictionInfluence.sum_weight_join (p : ℝ) (g : (ι → Bool) → ℝ) :
    (∑ z, weight p z * g z) =
      ∑ y : {i // ¬ P i} → Bool, weight p y *
        ∑ x : {i // P i} → Bool, weight p x * g (join P x y) := by sorry

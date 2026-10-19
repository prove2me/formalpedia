-- Prove2me | Theorems.Thm_OAI_Problem313_RestrictionInfluence_average_influence
-- name    : OAI.Problem313.RestrictionInfluence.average_influence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:22:38.549444+00:00
-- url     : https://prove2.me/theorems/6a4f348a-eb7f-4352-8ebe-286fb75a386d
-- title:
--   Averaging restricted influences recovers the influence
-- statement:
--   Let $\iota$ be a finite set of coordinates and $P$ a predicate splitting it into free coordinates $\{i:P(i)\}$ and exterior coordinates $\{i:\neg P(i)\}$. For a free configuration $x$ and an exterior configuration $y$, $\mathrm{join}(x,y)$ is the full configuration. The $p$-biased weight is $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$ on any coordinate set. For $f:\{0,1\}^\iota\to\{0,1\}$ and a free coordinate $i$, let $f_y=f(\mathrm{join}(\cdot,y))$ be the restriction with exterior $y$, and $I_i^p$ the pivotal influence. Then
--   $$
--   \sum_yw_p(y)\,I_i^p(f_y)=I_i^p(f) .
--   $$
--
--   Influences of free coordinates are preserved on average under random restrictions of the exterior.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RestrictionInfluence.lean#L86-L103

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

theorem OAI.Problem313.RestrictionInfluence.average_influence (p : ℝ) (f : (ι → Bool) → Bool) (i : {i // P i}) :
    (∑ y : {i // ¬ P i} → Bool,
      weight p y * influence p (fun x => f (join P x y)) i) =
        influence p f i.val := by sorry

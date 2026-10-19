-- Prove2me | Theorems.Thm_OAI_Problem313_RestrictionInfluence_join_update
-- name    : OAI.Problem313.RestrictionInfluence.join_update
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:22:02.418803+00:00
-- url     : https://prove2.me/theorems/5e5d88f8-44f6-4cd6-9120-96cb2f2037eb
-- title:
--   Updating a free coordinate commutes with joining
-- statement:
--   Let $\iota$ be a finite set of coordinates and $P$ a predicate splitting it into free coordinates $\{i:P(i)\}$ and exterior coordinates $\{i:\neg P(i)\}$. For a free configuration $x$ and an exterior configuration $y$, $\mathrm{join}(x,y)$ is the full configuration. The $p$-biased weight is $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$ on any coordinate set. For a free coordinate $i$ and a bit $b$,
--   $$
--   \mathrm{join}(x^{i\to b},y)=\mathrm{join}(x,y)^{i\to b} .
--   $$
--
--   Pivotality of a free coordinate for the restriction is the same as pivotality for the full function at the joined configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RestrictionInfluence.lean#L69-L84

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

omit [Fintype ι] in
theorem OAI.Problem313.RestrictionInfluence.join_update (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // P i}) (b : Bool) :
    join P (Function.update x i b) y = Function.update (join P x y) i.val b := by sorry

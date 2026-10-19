-- Prove2me | Theorems.Thm_OAI_Problem313_WeightedProjection_coefficient_synthesis
-- name    : OAI.Problem313.WeightedProjection.coefficient_synthesis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:35:32.85088+00:00
-- url     : https://prove2.me/theorems/48594b93-ddfb-4e51-89d5-b5166a1ea205
-- title:
--   Coefficients of a finite orthonormal expansion
-- statement:
--   Let $X$ be finite, $w$ a weight on $X$ and $(b_i)$ functions on $X$ that are orthonormal: $\sum_xw(x)b_i(x)b_j(x)=[i=j]$. For a finite index set $L$ and coefficients $c$, let $\Phi=\sum_{i\in L}c_ib_i$. Then for every index $i$,
--   $$
--   \langle\Phi,b_i\rangle_w=\sum_xw(x)\Phi(x)b_i(x)=\begin{cases}c_i,&i\in L,\\0,&i\notin L.\end{cases}
--   $$
--
--   Synthesis followed by analysis returns the coefficients. This is the defining property of an orthonormal system.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/ProjectionIdentities.lean#L34-L51

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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities

open OAI OAI.Problem313 OAI.Problem313.WeightedProjection
universe u v
open scoped BigOperators
variable {ι : Type u} {X : Type v} [Fintype X]

theorem OAI.Problem313.WeightedProjection.coefficient_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) (i : ι) :
    coefficient w basis (synthesis basis L c) i = if i ∈ L then c i else 0 := by sorry

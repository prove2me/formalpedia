-- Prove2me | Theorems.Thm_OAI_Problem313_low_degree_influence_bound
-- name    : OAI.Problem313.low_degree_influence_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:29:48.735999+00:00
-- url     : https://prove2.me/theorems/dd2d55fa-db0b-4444-a9dc-2d7c4d979eac
-- title:
--   Low-level mass is at most $m^{-1/4}$ times the total influence
-- statement:
--   Let $a_i\ge0$ with $\sum_ia_i=I$ and $a_i\le I/m$ for all $i$, where $m\ge1$. Let $0\le A\le1$ and $L\le1$ with
--   $$
--   L\le A\,m^{1/16}\sum_ia_i^{3/2} .
--   $$
--   Then $L\le m^{-1/4}I$.
--
--   Here $a_i$ are influences equalized by symmetry and $L$ is the low-level Fourier mass. The bound by $\sum a_i^{3/2}$ is the Talagrand–KKL-type estimate coming from hypercontractivity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeInfluence.lean#L43-L89

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

open OAI OAI.Problem313
universe u

theorem OAI.Problem313.low_degree_influence_bound {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hL1 : L ≤ 1)
    (hprojection : L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by sorry

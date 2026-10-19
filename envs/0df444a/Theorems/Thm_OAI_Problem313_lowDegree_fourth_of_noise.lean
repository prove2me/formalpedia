-- Prove2me | Theorems.Thm_OAI_Problem313_lowDegree_fourth_of_noise
-- name    : OAI.Problem313.lowDegree_fourth_of_noise
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:38:07.313255+00:00
-- url     : https://prove2.me/theorems/11f5d0dc-0fd0-484c-9571-d7a68522d133
-- title:
--   A fourth-moment bound for low-degree expansions
-- statement:
--   Let $X,\iota$ be finite, $w$ a weight on $X$, $(b_i)_{i\in\iota}$ functions on $X$ with degrees $\deg(i)\in\mathbb{N}$, and $0<\rho\le1$. Suppose that for every coefficient family $a$,
--   $$
--   \sum_xw(x)\Bigl(\sum_i\rho^{\deg(i)}a_ib_i(x)\Bigr)^4\le\Bigl(\sum_ia_i^2\Bigr)^2 .
--   $$
--   If $c$ is supported on degrees at most $k$, then $\sum_xw(x)\bigl(\sum_ic_ib_i(x)\bigr)^4\le\rho^{-4k}\bigl(\sum_ic_i^2\bigr)^2$.
--
--   A noise-operator $L^2\to L^4$ bound becomes an $L^4$ bound for low-degree functions, at the price $\rho^{-k}$ per norm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeL4.lean#L35-L71

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

open OAI OAI.Problem313
universe u v
open scoped BigOperators

theorem OAI.Problem313.lowDegree_fourth_of_noise
    {ι : Type u} {X : Type v} [Fintype ι] [Fintype X]
    (degree : ι → ℕ) (basis : ι → X → ℝ) (weight : X → ℝ)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : ι → ℝ,
      (∑ x, weight x * (∑ i, rho ^ (degree i : ℝ) * a i * basis i x) ^ 4) ≤
        (∑ i, (a i) ^ 2) ^ 2)
    (c : ι → ℝ) (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ x, weight x * (∑ i, c i * basis i x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ i, (c i) ^ 2) ^ 2 := by sorry

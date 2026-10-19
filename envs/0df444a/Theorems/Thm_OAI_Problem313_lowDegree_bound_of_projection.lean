-- Prove2me | Theorems.Thm_OAI_Problem313_lowDegree_bound_of_projection
-- name    : OAI.Problem313.lowDegree_bound_of_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:34:43.307625+00:00
-- url     : https://prove2.me/theorems/3c27d2b1-5b1f-440b-bc25-a5d9be2acb38
-- title:
--   The low-degree Fourier estimate from derivative projections
-- statement:
--   Let $\iota$ be finite, $0<\sigma\le\frac12$, $m\ge1$, $k=\sigma\log m/64$. Let $a\ge0$ on subsets with $\sum_Sa_S\le1$, $b_i\ge0$ on subsets for each $i$, and $J_i\ge0$ with $J_i\le\frac1m\sum_jJ_j$. Assume $a_S=\sigma^2b_i(S\setminus\{i\})$ for $i\in S$, and
--   $$
--   \sum_{|S|\le k}b_i(S)\le\Bigl(\frac\sigma4\Bigr)^{-2k}J_i^{3/2}\quad\text{for all }i .
--   $$
--   Then $\sum_{S\ne\emptyset,|S|\le k}a_S\le m^{-1/4}\sum_iJ_i$.
--
--   Instantiated with Fourier coefficients of a symmetric Boolean function and its derivatives, this bounds its low-level Fourier mass by a negative power of the symmetry orbit size times the total influence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeBounds.lean#L113-L157

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
open Finset

theorem OAI.Problem313.lowDegree_bound_of_projection
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (b : ι → Finset ι → ℝ) (J : ι → ℝ)
    (σ m : ℝ) (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m)
    (ha : ∀ S, 0 ≤ a S) (hb : ∀ i S, 0 ≤ b i S)
    (hJ : ∀ i, 0 ≤ J i) (horbit : ∀ i, J i ≤ (∑ j, J j) / m)
    (henergy : (∑ S : Finset ι, a S) ≤ 1)
    (hderiv : ∀ i S, i ∈ S → a S = σ ^ 2 * b i (S.erase i))
    (hprojection : ∀ i,
      (∑ S : Finset ι, if (S.card : ℝ) ≤ σ * Real.log m / 64 then b i S else 0) ≤
        (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) * (J i) ^ (3 / 2 : ℝ)) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ σ * Real.log m / 64 then a S else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, J i := by sorry

-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_project_inner
-- name    : OAI.Problem313.BiasedFourier.project_inner
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:41:34.766703+00:00
-- url     : https://prove2.me/theorems/74a4b9a5-d56d-40a5-ad9e-459ca9746cf8
-- title:
--   Pairing a function with its Fourier projection
-- statement:
--   Let $\iota$ be finite and $0<p<1$, with $p$-biased weight $w_p$, characters $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$, coefficients $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$, and projection $P_Lg=\sum_{S\in L}\hat g(S)\chi_S$ onto a family $L$ of supports. Then for every $g$ and every family $L$,
--   $$
--   \sum_xw_p(x)\,g(x)\,P_Lg(x)=\sum_{S\in L}\hat g(S)^2 .
--   $$
--
--   The pairing of a function with its projection equals the Fourier energy on $L$, which is also the energy of the projection itself.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean#L23-L42

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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u
open scoped BigOperators Classical
variable {ι : Type u} [Fintype ι]

theorem OAI.Problem313.BiasedFourier.project_inner (p : ℝ) (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * project p L g x) =
      ∑ S ∈ L, (coeff p g S) ^ 2 := by sorry

-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_synthesis_fourth_bound
-- name    : OAI.Problem313.BiasedFourier.synthesis_fourth_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:45:41.615309+00:00
-- url     : https://prove2.me/theorems/a6008bdf-53f5-40df-8c36-bb4381956f67
-- title:
--   Biased $(2,4)$-hypercontractivity
-- statement:
--   Let $\iota$ be finite and $0<p<1$, with $p$-biased weight $w_p$, characters $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$, coefficients $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$, and projection $P_Lg=\sum_{S\in L}\hat g(S)\chi_S$ onto a family $L$ of supports. Let $\rho=\sqrt{p(1-p)}/4$. Then for every coefficient family $c$ on subsets of $\iota$,
--   $$
--   \sum_xw_p(x)\Bigl(\sum_S\rho^{|S|}c_S\chi_S(x)\Bigr)^4\le\Bigl(\sum_Sc_S^2\Bigr)^2 .
--   $$
--
--   The noise operator $T_\rho$ maps $L^2(w_p)$ contractively into $L^4(w_p)$, for every finite number of coordinates and every bias.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierHypercontractive.lean#L96-L114

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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem OAI.Problem313.BiasedFourier.synthesis_fourth_bound {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (c : Finset ι → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by sorry

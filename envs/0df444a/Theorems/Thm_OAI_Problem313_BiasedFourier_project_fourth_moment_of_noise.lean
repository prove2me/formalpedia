-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_project_fourth_moment_of_noise
-- name    : OAI.Problem313.BiasedFourier.project_fourth_moment_of_noise
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:42:07.052357+00:00
-- url     : https://prove2.me/theorems/348d1c44-45f6-450a-a13e-f323c9172d5f
-- title:
--   Fourth moment of a low-degree Fourier projection
-- statement:
--   Let $\iota$ be finite and $0<p<1$, with $p$-biased weight $w_p$, characters $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$, coefficients $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$, and projection $P_Lg=\sum_{S\in L}\hat g(S)\chi_S$ onto a family $L$ of supports. Suppose $0<\rho\le1$ satisfies the coefficient-form hypercontractive estimate: for all coefficient families $a$,
--   $$
--   \sum_xw_p(x)\Bigl(\sum_S\rho^{|S|}a_S\chi_S(x)\Bigr)^4\le\Bigl(\sum_Sa_S^2\Bigr)^2 .
--   $$ If every $S\in L$ has $|S|\le k$, then
--   $$
--   \sum_xw_p(x)\,(P_Lg(x))^4\le\rho^{-4k}\Bigl(\sum_{S\in L}\hat g(S)^2\Bigr)^2 .
--   $$
--
--   The low-degree part of any function satisfies a reverse Hölder inequality between $L^4$ and $L^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean#L61-L92

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

theorem OAI.Problem313.BiasedFourier.project_fourth_moment_of_noise (p rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ x, weight p x * (project p L g x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ S ∈ L, (coeff p g S) ^ 2) ^ 2 := by sorry

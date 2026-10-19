-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_low_degree_estimate_of_noise
-- name    : OAI.Problem313.BiasedFourier.low_degree_estimate_of_noise
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:47:25.599008+00:00
-- url     : https://prove2.me/theorems/32cc6131-dd43-4363-b2da-24f5074a2770
-- title:
--   Symmetric Boolean functions have little low-degree Fourier mass
-- statement:
--   Let $\iota$ be finite and $0<p<1$, with $p$-biased weight $w_p$, characters $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$, coefficients $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$, and projection $P_Lg=\sum_{S\in L}\hat g(S)\chi_S$ onto a family $L$ of supports. Let $f:\{0,1\}^\iota\to\{0,1\}$, $m\ge1$, $\sigma=\sqrt{p(1-p)}$, and assume every influence satisfies $I_i^p(f)\le\frac1m\sum_jI_j^p(f)$, and the hypercontractive estimate holds with $\rho=\sigma/4$. Then
--   $$
--   \sum_{S\ne\emptyset,\ |S|\le\sigma\log m/64}\hat f(S)^2\le m^{-1/4}\sum_iI_i^p(f) .
--   $$
--
--   When influences are spread over orbits of size $m$, the Fourier mass on levels up to order $\log m$ is a negative power of $m$ times the total influence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegree.lean#L19-L61

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
open scoped BigOperators Classical
variable {ι : Type u} [Fintype ι]

theorem OAI.Problem313.BiasedFourier.low_degree_estimate_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, (Real.sqrt (p * (1 - p)) / 4) ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by sorry

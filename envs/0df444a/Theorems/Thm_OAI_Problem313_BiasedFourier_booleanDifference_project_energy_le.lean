-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_booleanDifference_project_energy_le
-- name    : OAI.Problem313.BiasedFourier.booleanDifference_project_energy_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:43:35.815599+00:00
-- url     : https://prove2.me/theorems/223008c2-390d-4e39-9db8-3c2a0e7c14f4
-- title:
--   Low-degree energy of a Boolean derivative is at most $I_i^{3/2}$
-- statement:
--   Let $\iota$ be finite and $0<p<1$, with $p$-biased weight $w_p$, characters $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$, coefficients $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$, and projection $P_Lg=\sum_{S\in L}\hat g(S)\chi_S$ onto a family $L$ of supports. Suppose $0<\rho\le1$ satisfies the coefficient-form hypercontractive estimate: for all coefficient families $a$,
--   $$
--   \sum_xw_p(x)\Bigl(\sum_S\rho^{|S|}a_S\chi_S(x)\Bigr)^4\le\Bigl(\sum_Sa_S^2\Bigr)^2 .
--   $$ For a Boolean function $f$, a coordinate $i$, and a family $L$ of supports of size at most $k$,
--   $$
--   \sum_{S\in L}\widehat{\Delta_if}(S)^2\le\rho^{-2k}\,I_i^p(f)^{3/2},
--   $$
--   where $\Delta_if(x)=[f(x^{i\to1})]-[f(x^{i\to0})]$ and $I_i^p(f)$ is the probability that $i$ is pivotal.
--
--   The low-degree part of each derivative is much smaller than its full energy $I_i^p(f)$ when the influence is small.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BooleanProjection.lean#L17-L46

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

theorem OAI.Problem313.BiasedFourier.booleanDifference_project_energy_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (f : (ι → Bool) → Bool) (i : ι)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p
      (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S) ^ 2) ≤
      rho ^ (-2 * k) * (Reindex.influence p f i) ^ (3 / 2 : ℝ) := by sorry

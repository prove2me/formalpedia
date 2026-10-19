-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_project_energy_le_of_noise
-- name    : OAI.Problem313.BiasedFourier.project_energy_le_of_noise
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:42:46.704239+00:00
-- url     : https://prove2.me/theorems/26254e3f-55e8-47e2-8b5b-65818f147f1f
-- title:
--   Low-degree energy of a $\{-1,0,1\}$-valued function
-- statement:
--   Let $\iota$ be finite and $0<p<1$, with $p$-biased weight $w_p$, characters $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$, coefficients $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$, and projection $P_Lg=\sum_{S\in L}\hat g(S)\chi_S$ onto a family $L$ of supports. Suppose $0<\rho\le1$ satisfies the coefficient-form hypercontractive estimate: for all coefficient families $a$,
--   $$
--   \sum_xw_p(x)\Bigl(\sum_S\rho^{|S|}a_S\chi_S(x)\Bigr)^4\le\Bigl(\sum_Sa_S^2\Bigr)^2 .
--   $$ If $g$ takes values in $\{-1,0,1\}$ and every $S\in L$ has $|S|\le k$, then
--   $$
--   \sum_{S\in L}\hat g(S)^2\le\rho^{-2k}\,\Pr_p[g\ne0]^{3/2} .
--   $$
--
--   A function with small support has little Fourier mass on low degrees. This is the analytic heart of the KKL and Talagrand inequalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean#L94-L118

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

theorem OAI.Problem313.BiasedFourier.project_energy_le_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 0 ∨ g x = 1)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p g S) ^ 2) ≤
      rho ^ (-2 * k) *
        (∑ x, if g x ≠ 0 then weight p x else 0) ^ (3 / 2 : ℝ) := by sorry

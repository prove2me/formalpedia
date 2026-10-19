-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_synthesis_fourth_option_of_split
-- name    : OAI.Problem313.BiasedFourier.synthesis_fourth_option_of_split
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:44:18.656114+00:00
-- url     : https://prove2.me/theorems/ee39746c-a4bb-4931-a7b0-9372352b7d16
-- title:
--   Tensorization step of biased hypercontractivity
-- statement:
--   Let $\iota$ be finite and $0<p<1$, with $p$-biased weight $w_p$, characters $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$, coefficients $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$, and projection $P_Lg=\sum_{S\in L}\hat g(S)\chi_S$ onto a family $L$ of supports. Let $\rho=\sqrt{p(1-p)}/4$. Assume the coefficient-form estimate
--   $$
--   \sum_xw_p(x)\Bigl(\sum_S\rho^{|S|}c_S\chi_S(x)\Bigr)^4\le\Bigl(\sum_Sc_S^2\Bigr)^2
--   $$
--   holds on $\iota$ for all $c$. Assume also that expectations over $\iota\sqcup\{\star\}$ split as $(1-p)$ times the slice $x_\star=0$ plus $p$ times the slice $x_\star=1$. Then the same estimate holds on $\iota\sqcup\{\star\}$.
--
--   Adding one coordinate preserves the $(2,4)$-hypercontractive inequality. Induction gives it on every finite product.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierHypercontractive.lean#L35-L83

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

theorem OAI.Problem313.BiasedFourier.synthesis_fourth_option_of_split {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hsplit : ∀ g : (Option ι → Bool) → ℝ,
      (∑ x, weight p x * g x) =
        (1-p) * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t false y)) +
        p * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t true y)))
    (ih : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
        c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2)
    (c : Finset (Option ι) → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by sorry

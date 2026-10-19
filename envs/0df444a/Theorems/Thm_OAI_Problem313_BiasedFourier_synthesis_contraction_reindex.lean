-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_synthesis_contraction_reindex
-- name    : OAI.Problem313.BiasedFourier.synthesis_contraction_reindex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:23:24.65881+00:00
-- url     : https://prove2.me/theorems/b742dbe2-7068-49c2-b684-3e7086c3a8cb
-- title:
--   Hypercontractivity in coefficient form transfers along bijections
-- statement:
--   Let $\iota$ be finite, $0<p<1$, and let $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$ be the $p$-biased Fourier coefficients, where $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$. Let $e:\iota\simeq\kappa$ be a bijection and $\rho\in\mathbb{R}$. Suppose that for all coefficient families $c$ on subsets of $\iota$,
--   $$
--   \sum_xw_p(x)\Bigl(\sum_S\rho^{|S|}c_S\chi_S(x)\Bigr)^4\le\Bigl(\sum_Sc_S^2\Bigr)^2 .
--   $$
--   Then the same inequality holds on $\kappa$ for all coefficient families $d$ on subsets of $\kappa$.
--
--   This lets the $(2,4)$-hypercontractive inequality be proved by induction over finite types, with the equivalence case handled here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierReindex.lean#L123-L144

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

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u v
open scoped BigOperators
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem OAI.Problem313.BiasedFourier.synthesis_contraction_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (hι : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * c S * char p S x) ^ 4) ≤
        (∑ S : Finset ι, (c S) ^ 2) ^ 2)
    (d : Finset κ → ℝ) :
    (∑ y, weight p y *
        (∑ T : Finset κ, ρ ^ T.card * d T * char p T y) ^ 4) ≤
        (∑ T : Finset κ, (d T) ^ 2) ^ 2 := by sorry

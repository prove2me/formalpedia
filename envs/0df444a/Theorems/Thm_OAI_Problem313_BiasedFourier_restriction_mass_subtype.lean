-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_restriction_mass_subtype
-- name    : OAI.Problem313.BiasedFourier.restriction_mass_subtype
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:25:19.830664+00:00
-- url     : https://prove2.me/theorems/ae610f1c-cdcd-4809-a2d9-40850f29e62f
-- title:
--   Average Fourier mass of restrictions
-- statement:
--   Let $\iota$ be finite, $0<p<1$, and let $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$ be the $p$-biased Fourier coefficients, where $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$. Let $P$ split $\iota$ into free and exterior coordinates, with restrictions $f_y$. For any function $L$ of free supports,
--   $$
--   \sum_yw_p(y)\sum_AL(A)\,\widehat{f_y}(A)^2=\sum_{S\subseteq\iota}L(S\cap\text{free})\,\hat f(S)^2 .
--   $$
--
--   On average over the exterior, the Fourier mass of the restriction at a free support $A$ equals the total mass of $f$ on supports whose free part is $A$. No condition is imposed on the exterior degree.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RestrictionMassSubtype.lean#L104-L130

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

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u
open scoped BigOperators
variable {ι : Type u} [Fintype ι] (P : ι → Prop) [DecidablePred P]

theorem OAI.Problem313.BiasedFourier.restriction_mass_subtype [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (L : Finset {i // P i} → ℝ) :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      ∑ A : Finset {i // P i}, L A * coeff p (restrictCube P f y) A ^ 2) =
      ∑ S : Finset ι, L (S.subtype P) * coeff p f S ^ 2 := by sorry

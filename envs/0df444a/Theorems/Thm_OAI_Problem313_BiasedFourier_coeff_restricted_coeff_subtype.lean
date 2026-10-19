-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_coeff_restricted_coeff_subtype
-- name    : OAI.Problem313.BiasedFourier.coeff_restricted_coeff_subtype
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:24:24.466001+00:00
-- url     : https://prove2.me/theorems/f8652089-dd03-436e-b5ce-11c29000ec8b
-- title:
--   Fourier coefficients of restrictions on a coordinate split
-- statement:
--   Let $\iota$ be finite, $0<p<1$, and let $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$ be the $p$-biased Fourier coefficients, where $\chi_S(x)=\prod_{i\in S}([x_i]-p)/\sqrt{p(1-p)}$. Let $P$ split $\iota$ into free and exterior coordinates, and for an exterior configuration $y$ let $f_y$ be the restriction of $f$. For a free support $A$ and an exterior support $D$,
--   $$
--   \widehat{\Bigl(y\mapsto\widehat{f_y}(A)\Bigr)}(D)=\hat f(A\sqcup D) .
--   $$
--
--   The exterior Fourier transform of a conditional coefficient is the full coefficient on the combined support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RestrictionMassSubtype.lean#L31-L49

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

theorem OAI.Problem313.BiasedFourier.coeff_restricted_coeff_subtype (p : ℝ) (f : (ι → Bool) → ℝ)
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    coeff p (fun y => coeff p (restrictCube P f y) A) D =
      coeff p f (subtypeSupport P A D) := by sorry

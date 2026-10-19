-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_coeff_insert_eq_sqrt_mul_delta
-- name    : OAI.Problem313.BiasedFourier.coeff_insert_eq_sqrt_mul_delta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:06:11.082316+00:00
-- url     : https://prove2.me/theorems/d900edf1-4ae8-4465-b2a8-0a0e2ae802af
-- title:
--   Fourier coefficients of a discrete derivative
-- statement:
--   Let $\iota$ be finite, $0<p<1$, and use the $p$-biased Fourier coefficients $\hat g(S)$. For $g:\{0,1\}^\iota\to\mathbb{R}$, a coordinate $i$ and $A\subseteq\iota$ with $i\notin A$,
--   $$
--   \hat g(A\cup\{i\})=\sqrt{p(1-p)}\ \widehat{\Delta_ig}(A),\qquad\Delta_ig(x)=g(x^{i\to1})-g(x^{i\to0}) .
--   $$
--
--   The derivative in direction $i$ shifts the Fourier support down by $i$ and scales by the standard deviation of a biased bit. This gives the Fourier formula for influences.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierDerivative.lean#L67-L108

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

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u
open scoped BigOperators
variable {ι : Type u} [DecidableEq ι]
variable [Fintype ι]

theorem OAI.Problem313.BiasedFourier.coeff_insert_eq_sqrt_mul_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (A : Finset ι) (hi : i ∉ A) :
    coeff p g (insert i A) =
      Real.sqrt (p * (1-p)) * coeff p (delta i g) A := by sorry

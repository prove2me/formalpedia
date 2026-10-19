-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_coeff_restricted_coeff
-- name    : OAI.Problem313.BiasedFourier.coeff_restricted_coeff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:49:13.520606+00:00
-- url     : https://prove2.me/theorems/6b09c4e8-d487-4ec4-84de-73ec6e38f2b4
-- title:
--   Fourier coefficients of restrictions recombine
-- statement:
--   Let $\iota,\kappa$ be finite, $p\in\mathbb{R}$, and $f$ a real function on $\{0,1\}^{\iota\sqcup\kappa}$, written $f(x,y)$ with $x\in\{0,1\}^\iota$, $y\in\{0,1\}^\kappa$. With $p$-biased Fourier coefficients $\hat{(\cdot)}$, for $A\subseteq\iota$ and $D\subseteq\kappa$
--   $$
--   \widehat{\Bigl(y\mapsto\widehat{f(\cdot,y)}(A)\Bigr)}(D)=\hat f(A\sqcup D) .
--   $$
--
--   Fixing the exterior variables and taking a Fourier coefficient in the free variables, then transforming in the exterior variables, recovers the full coefficient on the disjoint union.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierRestriction.lean#L15-L54

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u v
open scoped BigOperators
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]

theorem OAI.Problem313.BiasedFourier.coeff_restricted_coeff (p : ℝ) (f : (ι ⊕ κ → Bool) → ℝ)
    (A : Finset ι) (D : Finset κ) :
    coeff p (fun y => coeff p (fun x => f (Sum.elim x y)) A) D =
      coeff p f (A.disjSum D) := by sorry

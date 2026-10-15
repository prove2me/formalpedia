-- Prove2me | Theorems.Thm_OAI_ForestSpace_paired_polar_test
-- name    : OAI.ForestSpace.paired_polar_test
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:20:45.019028+00:00
-- url     : https://prove2.me/theorems/da01c7de-228d-4726-9507-db88c2ed959f
-- title:
--   Averaged dual norm bound from a pair of corrected test vectors
-- statement:
--   Let $V$ be a partially ordered set, let $c_{00}(V)$ be the space of finitely supported functions $V\to\mathbb{R}$ with the disjoint-segment norm, let $J(V)$ be its completion and $\iota:c_{00}(V)\to J(V)$ the canonical isometric embedding, and let $J(V)^*$ be the full continuous dual of $J(V)$ with the operator norm. Finitely supported vectors are identified with their images in $J(V)$, so $x(u)$ means $x(\iota u)$. For $A\subseteq V$, say that $x\in J(V)^*$ *annihilates* $A$ if $x(u)=0$ for every $u\in c_{00}(V)$ vanishing outside $A$.
--
--   **Theorem.** Let $H\subseteq V$ be any subset and $x,y\in J(V)^*$, where $x$ annihilates the complement $V\setminus H$ and $y$ annihilates $H$. Let $f,k,c\in c_{00}(V)$ with $f$ vanishing outside $H$ and $k,c$ vanishing on $H$, and let $s,d\in\mathbb{R}$ satisfy
--   $$
--   \|f+s(c+k)\|\le d\qquad\text{and}\qquad\|f+s(c-k)\|\le d .
--   $$
--   Then
--   $$
--   x(f)+s\,y(k)\le\frac{\|x+y\|+\|x-y\|}{2}\,d .
--   $$
--
--   The correction $c$ does not appear in the conclusion: it cancels when the evaluations of $x+y$ and $x-y$ are averaged. With $d=\sqrt{1+12s^2}$ from the paired corrected tests, and $f,k$ chosen to nearly norm $x$ and $y$, this yields the forest-space estimate $\sqrt{\|x\|^2+\|y\|^2/12}\le\tfrac12\bigl(\|x+y\|+\|x-y\|\bigr)$ behind the lower bound $\sqrt{1+t^2/12}-1$ for the averaged asymptotic midpoint modulus of the dual space.
--
--   **Formalization Note** "Annihilates" is `Annihilates x A`, quantifying over `TestVector V` supported on `A`; no lower-set assumption on $H$ is needed here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Polar.lean#L76-L98

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.paired_polar_test (H : Set V) {x y : FullDual V}
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H)
    {f k c : TestVector V} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hc : SupportedOn c Hᶜ) (s d : ℝ)
    (hp : ‖f + s • (c + k)‖ ≤ d) (hm : ‖f + s • (c - k)‖ ≤ d) :
    x (f : J V) + s * y (k : J V) ≤ (‖x+y‖ + ‖x-y‖) / 2 * d := by sorry

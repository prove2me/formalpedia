-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_inv_scale
-- name    : OAI.CliqueFreeIndependence.Numerical.inv_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:14:47.071001+00:00
-- url     : https://prove2.me/theorems/6852644d-2a96-4ec5-826d-492a487591a1
-- title:
--   Reciprocals of repeated squarings decay geometrically: $1/X^{2^n}\le 2^{-n}/X$ for $X\ge 2$
-- statement:
--   For a real number $X$ define the sequence of repeated squarings by $S_0(X)=X$ and $S_{n+1}(X)=S_n(X)^2$, so that $S_n(X)=X^{2^{n}}$. If $X\ge 2$, then for every natural number $n\ge 0$
--
--   $$
--   \frac{1}{S_n(X)}\le\Bigl(\frac12\Bigr)^{n}\frac{1}{X}.
--   $$
--
--   Thus along the scales $X, X^{2}, X^{4},\dots$ the reciprocals decrease at least geometrically with ratio $1/2$; as a consequence $\sum_{n\ge0}1/S_n(X)\le 2/X$. In the clique-free independence argument the scale parameter is squared at each stage of a multi-scale induction, and this inequality makes the additive error $1/S_{n}(X)$ incurred at stage $n$ small compared with the geometric gain $2^{-n}$ available at that stage.
--
--   **Formalization Note** The sequence is `scale X n`, defined by recursion on $n$ with `scale X 0 = X` and `scale X (n+1) = (scale X n)^2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Numerical.lean#L154-L168

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.Numerical
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Filter

theorem OAI.CliqueFreeIndependence.Numerical.inv_scale {X : ℝ} (hX : 2 ≤ X) (n : ℕ) :
    1 / scale X n ≤ (1/2 : ℝ)^n * (1/X) := by sorry

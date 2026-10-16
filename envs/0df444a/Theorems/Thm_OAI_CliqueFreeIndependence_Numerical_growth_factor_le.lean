-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_growth_factor_le
-- name    : OAI.CliqueFreeIndependence.Numerical.growth_factor_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:12:27.306425+00:00
-- url     : https://prove2.me/theorems/1a34b9e6-8123-489d-89cb-f0078b7d0890
-- title:
--   The growth factor $1+e^{x}/\tau(x)$ is at most $e^{4x}$ for $x\ge 32$
-- statement:
--   For a real number $x$ define the threshold $\tau(x)=\dfrac{1}{e^{x}\,x^{6}}$. If $x\ge 32$, then
--
--   $$
--   1+\frac{e^{x}}{\tau(x)}\le e^{4x}.
--   $$
--
--   Since $e^{x}/\tau(x)=e^{2x}x^{6}$, this is the elementary inequality $1+e^{2x}x^{6}\le e^{4x}$, valid for all real $x\ge 32$.
--
--   In the clique-free independence argument the quantity $1+L/t$ is the factor by which the weight of an iteratively enlarged neighbourhood ("reach set") can grow in one step, when all neighbour masses are at most $L$ and the step threshold is $t$. With $L=e^{x}$ and $t=\tau(x)$ this inequality shows that $n$ steps of enlargement cost at most a factor $e^{4xn}$.
--
--   **Formalization Note** The threshold is `threshold x = 1 / (Real.exp x * x ^ 6)`; for $x\ge 32$ it is strictly positive, so no division-by-zero convention is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Numerical.lean#L58-L75

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.Numerical
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v

theorem OAI.CliqueFreeIndependence.Numerical.growth_factor_le {x : ℝ} (hx : 32 ≤ x) :
    1 + Real.exp x / threshold x ≤ Real.exp (4 * x) := by sorry

-- Prove2me | Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_dyadic_ne_of_lt
-- name    : OAI.Problem310.GridSeparation.periodicKey_dyadic_ne_of_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:10:47.798073+00:00
-- url     : https://prove2.me/theorems/96a036f5-1546-4e37-a99d-d8c0ea002f44
-- title:
--   Distinct dyadic test points of one window lie in distinct periodic grid cells
-- statement:
--   For a real number $q>0$ and $x\in\mathbb{R}$, write $\{x\}=x-\lfloor x\rfloor\in[0,1)$ for the fractional part of $x$ and define the *periodic key* of $x$ at mesh $1/q$ as the integer
--   $$\kappa_q(x)=\bigl\lfloor q\,\{x\}\bigr\rfloor .$$
--   It records which of the cells $[k/q,(k+1)/q)$, $k=0,1,\dots$, of the unit interval contains $x$ modulo $1$.
--
--   Let $b,n,m$ be natural numbers with $3\le n<m\le b$, and let $x,t\in\mathbb{R}$ with $1\le t\le 2$. Then the points $x+t\,2^{-n}$ and $x+t\,2^{-m}$ have different periodic keys at mesh $2^{-(b+2)}$:
--   $$\kappa_{2^{b+2}}\bigl(x+t\,2^{-n}\bigr)\ne\kappa_{2^{b+2}}\bigl(x+t\,2^{-m}\bigr).$$
--
--   Consequently, for every center $x$ and every normalized scale $t\in[1,2]$, the test points $x+t\,2^{-n}$ with indices $n$ in the window $\{3,\dots,b\}$ fall into pairwise distinct cells of the periodic grid of mesh $2^{-(b+2)}$. The statement is uniform in $x$ and $t$: no centers close to cell boundaries have to be excluded. This is what allows the different test points of one window to read different entries of a random table indexed by grid cells, and hence to receive independent random labels.
--
--   **Formalization Note** The key is `periodicKey q x = ⌊q * Int.fract x⌋`, an integer; here $q=2^{b+2}$ is a real number and $2^{-n}$ is written `(2 : ℝ)⁻¹ ^ n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean#L105-L136

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation

open OAI OAI.Problem310 OAI.Problem310.GridSeparation
universe u_α

theorem OAI.Problem310.GridSeparation.periodicKey_dyadic_ne_of_lt {b n m : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnm : n < m) (hmhi : m ≤ b)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n) ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ m) := by sorry

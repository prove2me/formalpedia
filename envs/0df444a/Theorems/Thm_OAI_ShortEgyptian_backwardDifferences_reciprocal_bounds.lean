-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_backwardDifferences_reciprocal_bounds
-- name    : OAI.ShortEgyptian.backwardDifferences_reciprocal_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:22:41.327486+00:00
-- url     : https://prove2.me/theorems/fcd69b7a-a658-4c7e-9e51-b7d9c8c6bc09
-- title:
--   Two-sided bounds for iterated differences of the reciprocal function
-- statement:
--   For $h\in\mathbb{R}$ and $F:\mathbb{R}\to\mathbb{R}$ let $(D_hF)(x)=F(x)-F(x+h)$, and for a finite list $\mathbf h=(h_1,\dots,h_k)$ of real numbers let $D_{\mathbf h}F=D_{h_1}D_{h_2}\cdots D_{h_k}F$ be the iterated difference (for the empty list, $D_{\mathbf h}F=F$).
--
--   Let $\mathbf h=(h_1,\dots,h_k)$ be a list with $h_i\ge0$ for all $i$, and put $S=h_1+\cdots+h_k$ and $P=h_1h_2\cdots h_k$ (so $S=0$ and $P=1$ for the empty list). Let $x,U,V\in\mathbb{R}$ satisfy $0<U\le x$ and $x+S\le V$. Then the iterated difference of $y\mapsto1/y$ at $x$ satisfies
--
--   $$
--   \frac{P\,k!}{V^{k+1}}\le D_{\mathbf h}\Bigl(\frac1y\Bigr)(x)\le\frac{P\,k!}{U^{k+1}} .
--   $$
--
--   This is a discrete analogue of the formula $(-1)^k\frac{d^k}{dx^k}\frac1x=\frac{k!}{x^{k+1}}$: the $k$-fold difference lies between the values of $h_1\cdots h_k\,k!/\xi^{k+1}$ at the two ends $\xi=V$ and $\xi=U$ of a range containing $[x,x+S]$. Such two-sided bounds make second-derivative exponential-sum estimates applicable to differenced phases of the form $Z/n$.
--
--   **Formalization Note** $D_{\mathbf h}F$ is `backwardDifferences hs F`, defined by `backwardDifferences (h :: hs) F x = backwardDifferences hs F x - backwardDifferences hs F (x + h)`. The bounds are written with $(1/V)^{k+1}$ and $(1/U)^{k+1}$, and $k!$ is cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ReciprocalDifferences.lean#L168-L193

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.backwardDifferences_reciprocal_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x U V : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x + hs.sum ≤ V) :
    hs.prod * hs.length.factorial * (1 / V) ^ (hs.length + 1) ≤
        backwardDifferences hs (fun y => 1 / y) x ∧
      backwardDifferences hs (fun y => 1 / y) x ≤
        hs.prod * hs.length.factorial * (1 / U) ^ (hs.length + 1) := by sorry

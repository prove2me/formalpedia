-- Prove2me | Theorems.Thm_LeightonRao_Directed_corollary_14
-- name    : LeightonRao.Directed.corollary_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:39.971536+00:00
-- url     : https://prove2.me/theorems/59fc2cf1-6bdc-46e8-b527-b3f81bf0f850
-- title:
--   Corollary 14, p. 806 — either a node with in- and out-balls of radius 1/4n² of size ≥ 2n/3, or a directed cut of ratio cost O(W log n)
-- statement:
--   Let $G$ be a directed network on $n\ge2$ nodes and $d\ge0$ a distance function with total weight $W$. Put $\Delta=1/(4n^2)$. Then either
--
--   1. there is a node $v$ with $|\mathcal N^{\Delta}_{\mathrm{in}}(v,G)|\ge 2n/3$ and $|\mathcal N^{\Delta}_{\mathrm{out}}(v,G)|\ge 2n/3$, or
--   2. there is a nonempty proper $U\subsetneq V$ whose directed cut has ratio cost
--   $$\frac{C(U,\bar U)}{|U|\,|\bar U|}\le\frac{8W\log n}{\Delta\,(n/6)(5n/6)}=\frac{1152}{5}\,W\log n.$$
--
--   This is the dichotomy that drives Lemma 16.
--
--   **Formalization Note** The paper states option 2 as "ratio cost $O(W\log n)$"; the explicit bound is the display computed in the proof on p. 806. Polynomial-time findability is not formalized: "we can find" is existence.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 806, Corollary 14 and the display in its proof

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Corollary 14, p. 806. With `Δ = 1/(4n²)`, either some node `v` has
`|𝒩^Δ_in(v)| ≥ 2n/3` and `|𝒩^Δ_out(v)| ≥ 2n/3`, or some directed cut has ratio cost at most
`8 W log₂ n / (Δ (n/6)(5n/6))` (the bound computed in the proof, `= (1152/5) W log₂ n`). -/
theorem corollary_14 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) :
    let n : ℝ := (Fintype.card V : ℝ)
    let Δ : ℝ := 1 / (4 * n ^ 2)
    (∃ v, 2 * n ≤ 3 * ((inBall N d v Δ).card : ℝ) ∧
        2 * n ≤ 3 * ((outBall N d v Δ).card : ℝ)) ∨
    (∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
        diRatio N U ≤ 8 * diTotalWeight N d * Real.logb 2 n / (Δ * (n / 6) * (5 * n / 6))) := by sorry

end LeightonRao.Directed

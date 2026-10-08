-- Prove2me | Theorems.Thm_LeightonRao_Directed_lemma_13
-- name    : LeightonRao.Directed.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:20.146994+00:00
-- url     : https://prove2.me/theorems/e9bb24c5-5626-49d2-823c-0675ae07fb2c
-- title:
--   Lemma 13, p. 804 — ordered partition whose backward edges cost ≤ 8W log n/Δ, each part inside an in- and out-ball of radius Δ
-- statement:
--   Let $G=(V,E)$ be a directed network with arbitrary nonnegative capacities on $n$ nodes, let $\Delta>0$, and let $d\ge0$ be a distance function with total weight $W$. Then $V$ can be partitioned into nonempty sets $V_1,\dots,V_r$ such that
--
--   1. the total capacity of the edges directed from a later part to an earlier part satisfies
--   $$\sum_{1\le j<i\le r}\ \sum_{u\in V_i,\,v\in V_j}C(u,v)\le\frac{8W\log n}{\Delta};$$
--   2. for each $i\le r$ there is a node $v\in V_i$ with $|\mathcal N^\Delta_{\mathrm{in}}(v,G)|\ge|V_i|$ and $|\mathcal N^\Delta_{\mathrm{out}}(v,G)|\ge|V_i|$.
--
--   Here $\log$ is base $2$. This is the directed region-growing decomposition; Corollary 14 turns it into either a large in/out-ball or a sparse directed cut.
--
--   **Formalization Note** The partition is a labelling $V\to\{1,\dots,r\}$; condition 2 makes every part nonempty. The printed condition (1) reads "$1\le j<i<r$"; the proof (p. 805) and Corollary 14 use $1\le j<i\le r$, which is what is stated. The last line of the printed proof (p. 806) writes $|\mathcal N^\Delta_{\mathrm{out}}(v,G)|\le|V_i|$; the statement's $\ge$ is used here. No connectivity is assumed (the balls are defined through walks), matching "any directed graph".
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 804, Lemma 13 (proof pp. 804–806)

import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Lemma 13, p. 804. For any directed network, any `Δ > 0` and any nonnegative
distance function of total weight `W`, there is an ordered partition `V₁, …, V_r` of `V`
(`V_i = {x | lab x = i}`) such that
(1) the edges directed from a later part to an earlier part (`u ∈ V_i`, `v ∈ V_j`, `j < i ≤ r`) have
total capacity at most `8 W log₂ n / Δ`, and
(2) every part `V_i` contains a node `v` with `|𝒩^Δ_in(v)| ≥ |V_i|` and `|𝒩^Δ_out(v)| ≥ |V_i|`
(in particular every part is nonempty). -/
theorem lemma_13 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (r : ℕ) (lab : V → Fin r),
      (∑ u, ∑ v, if lab v < lab u then N.C u v else 0) ≤
        8 * diTotalWeight N d * Real.logb 2 (Fintype.card V) / Δ ∧
      ∀ i : Fin r, ∃ v, lab v = i ∧
        (Finset.univ.filter (fun x => lab x = i)).card ≤ (inBall N d v Δ).card ∧
        (Finset.univ.filter (fun x => lab x = i)).card ≤ (outBall N d v Δ).card := by sorry

end LeightonRao.Directed

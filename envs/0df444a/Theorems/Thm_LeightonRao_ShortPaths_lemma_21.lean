-- Prove2me | Theorems.Thm_LeightonRao_ShortPaths_lemma_21
-- name    : LeightonRao.ShortPaths.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:41.504099+00:00
-- url     : https://prove2.me/theorems/d4d02066-8b78-4898-b610-a40b7d235740
-- title:
--   Lemma 21, p. 809 — restricted distance from a large vertex set
-- statement:
--   Let $G$ be a connected capacitated graph on $n\ge2$ vertices, with uniform sparsest cut value $\mathcal S>0$ and maximum incident capacity $C_{\max}$. Let $d$ be a nonnegative symmetric distance function of total weight $W$, and let $T\subseteq V$ contain at least $2n/3$ vertices. If $L$ is a real number satisfying $L\ge12C_{\max}\ln n/(n\mathcal S)$, then, with distances restricted to paths of at most $L/4$ edges,
--
--   $$\sum_{u\in V\setminus T}d_{L/4}(T,u)\le\frac{6W}{n\mathcal S}.$$
--
--   In particular, all restricted distances in this sum are finite. The estimate links the large component to vertices outside it.
--
--   **Formalization Note** The logarithm in the hypothesis is natural $\ln n$, while other bounds in the paper use base-two $\log n$. Restricted distances take values in the extended nonnegative reals.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 809, Lemma 21

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- Lemma 21, p. 809. The length `L` is real, as on the page; `d(T, u)` uses walks with at most
`L / 4` edges. The restricted distances are extended nonnegative reals. -/
theorem lemma_21 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (L : ℝ)
    (hL : 12 * cmax N * Real.log (Fintype.card V : ℝ) /
      ((Fintype.card V : ℝ) * minCut N) ≤ L)
    (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ)) :
    ∑ u ∈ Tᶜ, distFromL N d (L / 4) T u ≤
      ENNReal.ofReal (6 * totalWeight N d /
        ((Fintype.card V : ℝ) * minCut N)) := by sorry

end LeightonRao.ShortPaths

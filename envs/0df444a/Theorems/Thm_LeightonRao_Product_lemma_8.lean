-- Prove2me | Theorems.Thm_LeightonRao_Product_lemma_8
-- name    : LeightonRao.Product.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:58.004487+00:00
-- url     : https://prove2.me/theorems/c6bf1c25-5052-4690-92d6-d2cff21f1278
-- title:
--   Lemma 8, p. 802 — partition G so that components meeting 𝒫 have radius ≤ Δ and the cut capacity is at most 4W log p/Δ
-- statement:
--   Let $G$ be a capacitated network on $V$, let $d$ be a distance function with total weight $W$, let $\pi:V\to\mathbb R$ be a node weighting whose support $\mathcal P=\{u:\pi(u)\ne0\}$ has $p\ge2$ nodes, and let $\Delta>0$. Then $V$ can be partitioned into components so that
--
--   1. every component containing a node of $\mathcal P$ has radius at most $\Delta$ (measured by walks inside the component), and
--   2. the total capacity of the edges joining different components is at most
--   $$\frac{4W\log_2 p}{\Delta}.$$
--
--   This is the region-growing decomposition of Lemma 3 with $n$ replaced by the number $p$ of weighted nodes; it is the source of the $\log p$ (hence $\log k$) factor in Theorem 7.
--
--   **Formalization Note** The page says "any $\Delta\ge0$", but the bound divides by $\Delta$; as in Lemma 3 we require $\Delta>0$. The page allows any $p$, but for $p=1$ the bound is $0$ and the statement fails on a single edge (its weighted endpoint must have a component of small radius, so the edge is cut); we require $p\ge2$, which is the only case Theorem 7 uses. $\log$ is $\log_2$ (footnote 3). The existence of the partition is formalized; its polynomial-time construction is not.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 802, Lemma 8

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem lemma_8 {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (π : V → ℝ) (hp : 2 ≤ (support π).card) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, (∃ x ∈ S, π x ≠ 0) → HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d * Real.logb 2 ((support π).card : ℝ) / Δ := by sorry

end LeightonRao.Product

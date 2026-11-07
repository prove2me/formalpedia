-- Prove2me | Theorems.Thm_HZTractability_lemma_2_3
-- name    : HZTractability.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:41.74118+00:00
-- url     : https://prove2.me/theorems/1caf29e5-d8e8-4049-b684-312ffaba9fec
-- title:
--   Lemma 2.3 — equalizing prices within a group preserves a normalized additive $\varepsilon$-equilibrium
-- statement:
--   Let $(p,x)$ be a normalized additive $\varepsilon$-equilibrium ($\varepsilon\ge0$) of an HZ market with utilities in $[0,1]$, and let $S$ be a nonempty **group**: a set of goods with identical utility vectors, $u_{ij}=u_{ik}$ for every buyer $i$ and all $j,k\in S$. Define $p'$ by
--   $$
--   p'_j=\min_{k\in S}p_k\ \ (j\in S),\qquad p'_j=p_j\ \ (j\notin S).
--   $$
--   Then $(p',x)$, with the same allocation $x$, is a normalized additive $\varepsilon$-equilibrium. Moreover $\min_{j\in S}p'_j=\min_{j\in S}p_j$, and the minimum over every nonempty set of goods disjoint from $S$ (every other group) is unchanged.
--
--   The lemma lets the analysis use one price per group.
--
--   Differences from the source:
--   - encoding: a group (distinct unit-supply goods with identical utility vectors, §2.3) and “the same group minima” → a nonempty finite set $S$ of goods with identical columns; the minimum over $S$ and over every nonempty set disjoint from $S$ is unchanged; reason: the paper's groups are disjoint sets with identical columns
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma 2.3, p.7 (PDF p.9); groups, §2.3, p.7

import Mathlib
import Definitions.Def_HZTractability_IsNormAddEq

namespace HZTractability

/-- **Lemma 2.3 (Equalizing prices within a group)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.7 (PDF 9)): "Replacing all prices in a group by
their minimum, while keeping the allocation fixed, preserves a normalized additive ε-equilibrium
with the same error and the same group minima."

Let `S` be a nonempty group: a set of goods on which every buyer's utility is constant (§2.3, p.7).
If `(x, p)` is a normalized additive ε-equilibrium, then so is `(x, p')`, where `p'` sets every
price in `S` to `min_{k∈S} p_k` and leaves the other prices unchanged. The minimum over `S`, and the
minimum over every nonempty set of goods disjoint from `S` (every other group), are the same for `p'`
as for `p`.

**Formalization Note** The market is any finite HZ market with utilities in `[0, 1]` (§2.2, p.7)
and `ε ≥ 0` (Definition 2.2). -/
theorem lemma_2_3 {B G : Type} [Fintype B] [Fintype G] [DecidableEq G] (u : B → G → ℝ)
    (hu : ∀ i j, 0 ≤ u i j ∧ u i j ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (x : B → G → ℝ) (p : G → ℝ) (S : Finset G) (hS : S.Nonempty)
    (hgrp : ∀ i, ∀ j ∈ S, ∀ k ∈ S, u i j = u i k)
    (heq : IsNormAddEq u ε x p) :
    IsNormAddEq u ε x (fun j => if j ∈ S then S.inf' hS p else p j) ∧
      S.inf' hS (fun j => if j ∈ S then S.inf' hS p else p j) = S.inf' hS p ∧
      ∀ (T : Finset G) (hT : T.Nonempty), Disjoint S T →
        T.inf' hT (fun j => if j ∈ S then S.inf' hS p else p j) = T.inf' hT p := by sorry

end HZTractability

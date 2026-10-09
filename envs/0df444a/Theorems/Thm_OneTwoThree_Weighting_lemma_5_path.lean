-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_5_path
-- name    : OneTwoThree.Weighting.lemma_5_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:56.282145+00:00
-- url     : https://prove2.me/theorems/ee289f01-40c5-4ad2-be91-c0ba55634423
-- title:
--   Lemma 5 (i)–(vi) — the bipartite weighting of Lemma 5 with additional control along a fixed path $p$
-- statement:
--   Assume the setting of Lemma 5: $G=(V,E)$ is a finite connected bipartite graph with parts $B$ and $R=V\setminus B$, $\alpha:B\to\mathbb N$ satisfies $\alpha(v)\in\{2\deg(v)-1,2\deg(v),2\deg(v)+1\}$ for $v\in B$, and $R'\subseteq R$ has $|R'|+\sum_{v\in B}\alpha(v)$ even. Moreover let $p=(v_1,\dots,v_k)$ be a fixed path in $G$ with $k\ge 3$ vertices and $v_1,v_k\in B$. Then there exists an edge-weighting $\omega:E\to\{1,2,3\}$ satisfying (i)–(iii) of Lemma 5 ($s_\omega$ even on $R\setminus R'$, odd on $R'$, equal to $\alpha$ on $B$) and in addition
--
--   4. $\omega(\{v_1,v_2\})\ne 1$ if $\alpha(v_1)=2\deg(v_1)+1$, and $\omega(\{v_1,v_2\})\ne 3$ otherwise;
--   5. for each $1<i<k$ with $v_i\in B$,
--   $$\omega(\{v_{i-1},v_i\})+\omega(\{v_i,v_{i+1}\})\in\{3,4,5\};$$
--   6. $\omega(\{v_{k-1},v_k\})\ne 1$ if $\alpha(v_k)=2\deg(v_k)+1$, and $\omega(\{v_{k-1},v_k\})\ne 3$ otherwise.
--
--   These extra properties allow the weights along $p$ to be shifted by $\pm1$ later without destroying the weighted degrees; this is how Lemma 9 resolves its last coloring conflict.
--
--   **Formalization Note** The path is a walk `p : G.Walk a b` with `p.IsPath` and length at least $2$ (that is, $k\ge3$ vertices), with $a=v_1$, $b=v_k$ in $B$. Vertex $v_i$ is `p.getVert (i-1)`, so (v) ranges over the indices $0<j<$ length with `p.getVert j ∈ B`. Each "otherwise" clause is a separate implication. All six properties hold for one and the same $\omega$. This is a separate item from Lemma 5 (i)–(iii) because Lemmas 7 and 8 apply Lemma 5 without a path.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 6, Lemma 5 (i)–(vi), including the paragraph "Moreover, let p = {v1, . . . , vk} be a fixed path ..."

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_5_path {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (B : Finset V)
    (hB : ∀ u v, G.Adj u v → (u ∈ B ↔ v ∉ B)) (α : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (G.degree v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (G.degree v : ℤ) ∨
      (α v : ℤ) = 2 * (G.degree v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ) (hpar : Even (#R' + ∑ v ∈ B, α v))
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hk : 2 ≤ p.length) (ha : a ∈ B) (hb : b ∈ B) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ Bᶜ \ R', Even (wdeg G ω v)) ∧
      (∀ v ∈ R', Odd (wdeg G ω v)) ∧
      (∀ v ∈ B, wdeg G ω v = α v) ∧
      -- (iv)
      (α a = 2 * G.degree a + 1 → ω s(p.getVert 0, p.getVert 1) ≠ 1) ∧
      (α a ≠ 2 * G.degree a + 1 → ω s(p.getVert 0, p.getVert 1) ≠ 3) ∧
      -- (v)
      (∀ j, 0 < j → j < p.length → p.getVert j ∈ B →
        ω s(p.getVert (j - 1), p.getVert j) + ω s(p.getVert j, p.getVert (j + 1)) ∈
          ({3, 4, 5} : Finset ℕ)) ∧
      -- (vi)
      (α b = 2 * G.degree b + 1 → ω s(p.getVert (p.length - 1), p.getVert p.length) ≠ 1) ∧
      (α b ≠ 2 * G.degree b + 1 → ω s(p.getVert (p.length - 1), p.getVert p.length) ≠ 3) := by sorry

end OneTwoThree.Weighting

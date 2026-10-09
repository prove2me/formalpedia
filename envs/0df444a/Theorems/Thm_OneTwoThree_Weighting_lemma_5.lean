-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_5
-- name    : OneTwoThree.Weighting.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:30.545162+00:00
-- url     : https://prove2.me/theorems/18cd221d-d23a-4ae5-97c8-ca2db074a231
-- title:
--   Lemma 5 (i)–(iii) — a bipartite $\{1,2,3\}$-weighting with prescribed parities on $R$ and $s_\omega=\alpha$ on $B$
-- statement:
--   Let $G=(V,E)$ be a finite connected bipartite graph with parts $B$ and $R=V\setminus B$ (every edge joins $B$ to $R$). Let $\alpha:B\to\mathbb N$ satisfy
--   $$\alpha(v)\in\{2\deg(v)-1,\ 2\deg(v),\ 2\deg(v)+1\}\qquad\text{for all }v\in B,$$
--   and let $R'\subseteq R$ be such that $|R'|+\sum_{v\in B}\alpha(v)$ is even. Then there exists an edge-weighting $\omega:E\to\{1,2,3\}$ such that
--
--   1. $s_\omega(v)$ is even for all $v\in R\setminus R'$,
--   2. $s_\omega(v)$ is odd for all $v\in R'$, and
--   3. $s_\omega(v)=\alpha(v)$ for all $v\in B$.
--
--   The lemma weights the red-blue edges: blue vertices receive exactly the missing amount $\alpha(v)$ and red vertices receive prescribed parities.
--
--   **Formalization Note** $R$ is the complement of $B$ and bipartiteness is the condition that every edge has exactly one end in $B$. $\alpha$ is typed $V\to\mathbb N$, but only its values on $B$ occur. The membership $\alpha(v)\in\{2\deg(v)-1,2\deg(v),2\deg(v)+1\}$ is stated in $\mathbb Z$, so no truncated subtraction appears; $\deg$ is the degree in $G$.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 6, Lemma 5 (i)–(iii)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (B : Finset V)
    (hB : ∀ u v, G.Adj u v → (u ∈ B ↔ v ∉ B)) (α : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (G.degree v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (G.degree v : ℤ) ∨
      (α v : ℤ) = 2 * (G.degree v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ) (hpar : Even (#R' + ∑ v ∈ B, α v)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ Bᶜ \ R', Even (wdeg G ω v)) ∧
      (∀ v ∈ R', Odd (wdeg G ω v)) ∧
      (∀ v ∈ B, wdeg G ω v = α v) := by sorry

end OneTwoThree.Weighting

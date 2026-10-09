-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_3
-- name    : OneTwoThree.Weighting.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:25.476365+00:00
-- url     : https://prove2.me/theorems/7b1b901f-f349-4169-93e1-61ff968553c9
-- title:
--   Lemma 3 — for even $h$, a $\{1,2,3\}$-weighting and odd proper $f$ with $|s_\omega(v)+h(v)-f(v)|=1$
-- statement:
--   Let $G=(V,E)$ be a finite, not necessarily connected graph and let $h:V\to\{0,2,4,\dots\}$ take only even values. Then there exist an edge-weighting $\omega:E\to\{1,2,3\}$ and a function $f:V\to\{1,3,5,\dots\}$ taking only odd values such that
--
--   1. $f(v)\ne f(w)$ for every edge $\{v,w\}\in E$, and
--   2. for every vertex $v\in V$,
--   $$|s_\omega(v)+h(v)-f(v)|=1.$$
--
--   In the proof of Theorem 1 the lemma is applied to the blue subgraph $G[B]$ with $h(v)=2\deg_R(v)$: it fixes the weights inside $B$ and odd "designated colors" $f$ that already form a proper coloring of $G[B]$, up to an error of exactly one that is corrected later on the red-blue edges.
--
--   **Formalization Note** $h$ and $f$ are $\mathbb N$-valued; "only odd values" in $\mathbb N$ is exactly values in $\{1,3,5,\dots\}$. The absolute value is taken in $\mathbb Z$, since $s_\omega(v)+h(v)-f(v)$ may equal $-1$.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 3, Lemma 3

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

open Finset SimpleGraph

theorem lemma_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : V → ℕ) (hh : ∀ v, Even (h v)) :
    ∃ (ω : Sym2 V → ℕ) (f : V → ℕ), IsWeighting G 3 ω ∧ (∀ v, Odd (f v)) ∧
      (∀ v w, G.Adj v w → f v ≠ f w) ∧
      ∀ v, |(wdeg G ω v : ℤ) + (h v : ℤ) - (f v : ℤ)| = 1 := by sorry

end OneTwoThree.Weighting

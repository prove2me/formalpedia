-- Prove2me | Theorems.Thm_LefebvreVariations_ch3_small_separator
-- name    : LefebvreVariations.ch3_small_separator
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-23T23:29:16.356914+00:00
-- url     : https://prove2.me/theorems/551ab269-1060-4a36-a6bd-8b9998c3bd6c
-- title:
--   Lefebvre's variations, No. 1 — on a theme by Caccetta and Häggkvist: Caccetta–Häggkvist ($r=3$) with a small out-separator
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the *small out-separator* case of the Caccetta–Häggkvist conjecture for minimum out-degree $3$.
--
--   Let $D$ be a finite loopless digraph on a vertex set $V$ with $n = |V|$ vertices, without multiple arcs (directed $2$-cycles are allowed). Suppose every vertex has out-degree at least $3$:
--
--   $$
--   d^+(v) = \bigl|\{\, w \in V : v \to w \,\}\bigr| \ge 3 \qquad \text{for every } v \in V.
--   $$
--
--   For $S \subseteq V$, write
--
--   $$
--   \partial^+ S = \{\, y \in V \setminus S : x \to y \text{ for some } x \in S \,\}
--   $$
--
--   for the out-boundary of $S$: the vertices outside $S$ that receive an arc from $S$. Assume there is a nonempty set $S \subseteq V$ such that
--
--   1. $1 \le |\partial^+ S| \le 2$, and
--   2. $S \cup \partial^+ S \ne V$, so that some vertex lies neither in $S$ nor in its out-boundary.
--
--   Then $D$ contains a directed cycle of length $\ell$ with
--
--   $$
--   2 \le \ell \qquad\text{and}\qquad 3\ell < n + 3, \quad\text{that is,}\quad \ell \le \left\lceil \frac{n}{3} \right\rceil .
--   $$
--
--   The Caccetta–Häggkvist conjecture asserts that every digraph on $n$ vertices with minimum out-degree $r \ge 1$ has a directed cycle of length at most $\lceil n/r \rceil$. For $r = 3$ this is a theorem of Hamidoune (1987), and the statement above is the special case of it in which $\partial^+ S$ is a vertex cut of order one or two separating the nonempty set $S$ from the rest of the digraph. This is exactly the configuration that remains when the case $r = 3$ is proved by strong induction on $n$. Digraphs in which every such out-boundary has at least three vertices are handled by growing out-balls, and sets with empty out-boundary by induction on a smaller digraph.
--
--   **Formalization Note** The digraph is a `Digraph V` on a finite type, with looplessness as a hypothesis and out-degree `Digraph.outDegree` (the cardinality of the out-neighbour set). A directed cycle of length $\ell$ is `Digraph.HasCycleOfLength ℓ`: an injective map $f : \mathbb{Z}/\ell \to V$ with $f(i) \to f(i+1)$ for every $i$. The conclusion $\ell \cdot 3 < |V| + 3$ is the form used in `CaccettaHaggkvistFor`. The out-boundary is written inline as a `Finset.filter`, and the decidability instances it needs are hypotheses of the theorem, so the statement holds for every choice of them. No `Nonempty V` hypothesis is needed, since $S$ is nonempty.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement the Caccetta–Häggkvist conjecture for minimum out-degree $r=3$ (Hamidoune 1987; platform statement `TenChallenges.challenge_03_r3`). A strong-induction proof of the base statement splits into three cases: out-boundaries with at least $3$ vertices (ball growth), sets with empty out-boundary (induction on a smaller digraph), and the remaining case, a nonempty $S$ with $1 \le |\partial^+ S| \le 2$ and $S \cup \partial^+ S \ne V$. This statement is exactly that remaining case. It is a special case of the base statement (the conclusion is the same, the hypothesis is stronger), and the base statement follows from it together with the two other cases.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). Special case of: Y. O. Hamidoune, A note on minimal directed graphs with given girth, J. Combin. Theory Ser. B 43 (1987), no. 3, 343–348, which proves the Caccetta–Häggkvist conjecture for minimum out-degree r = 3 (every loopless digraph on n vertices with minimum out-degree 3 has a directed cycle of length at most ⌈n/3⌉). Here the conclusion is restricted to digraphs having a nonempty set S with 1 ≤ |∂⁺S| ≤ 2 and S ∪ ∂⁺S ≠ V. Conjecture: L. Caccetta and R. Häggkvist, On minimal digraphs with given girth, Congr. Numer. 21 (1978), 181–187. Origin of this statement: it is the remaining case of a reduction of TenChallenges.challenge_03_r3 (Caccetta–Häggkvist, r = 3). That reduction uses strong induction on n, a ball-growth argument when every out-boundary that does not cover the digraph has at least 3 vertices, and the induction hypothesis on the subdigraph induced by a nonempty set with empty out-boundary.

import Definitions.Def_TenChallenges_CaccettaHaggkvist

set_option autoImplicit false

namespace LefebvreVariations
theorem ch3_small_separator {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, 3 ≤ G.outDegree v)
    (S : Finset V) (hS : S.Nonempty)
    (hpos : 1 ≤ (Finset.univ.filter fun y => y ∉ S ∧ ∃ x ∈ S, G.Adj x y).card)
    (hsmall : (Finset.univ.filter fun y => y ∉ S ∧ ∃ x ∈ S, G.Adj x y).card ≤ 2)
    (hcov : S ∪ Finset.univ.filter (fun y => y ∉ S ∧ ∃ x ∈ S, G.Adj x y) ≠ Finset.univ) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * 3 < Fintype.card V + 3 ∧ G.HasCycleOfLength ℓ := by sorry
end LefebvreVariations

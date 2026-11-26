-- Prove2me | Theorems.Thm_LefebvreVariations_caccetta_haggkvist_three_card_le_nine
-- name    : LefebvreVariations.caccetta_haggkvist_three_card_le_nine
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:48:16.837819+00:00
-- url     : https://prove2.me/theorems/c6b9f029-5958-5868-ab64-e83bee123740
-- title:
--   Lefebvre's variations, No. 86 — on a theme by Caccetta and Häggkvist: the Caccetta-Haggkvist conjecture with out-degree 3 holds for digraphs on at most 9 vertices
-- statement:
--   Let $G$ be a loopless digraph on $n$ vertices with $1\le n\le 9$ in which every vertex has out-degree at least $3$. Then $G$ contains a directed cycle of length $\ell$ with $3\ell< n+3$, that is, of length at most $\lceil n/3\rceil$.
--
--   Concretely: a $2$-cycle when $n\le 6$, and a cycle of length $2$ or $3$ when $7\le n\le 9$. (For $n\le 3$ the hypothesis cannot be met.) This is the Caccetta–Häggkvist conjecture for out-degree $r=3$ restricted to at most $9$ vertices; it stops at $9$ because for $n=10$ there is a digraph of minimum out-degree $3$ with no cycle of length $2$ or $3$, so the bound $\lceil 10/3\rceil=4$ is genuinely needed there.
--
--   **Formalization Note** The statement is the conclusion of `CaccettaHaggkvistFor 3` in the platform definitions `Def_TenChallenges_CaccettaHaggkvist`, with the extra hypothesis `Fintype.card V ≤ 9`: for a `Digraph V` with `∀ v, ¬ G.Adj v v` and `∀ v, 3 ≤ G.outDegree v` there is `ℓ` with `2 ≤ ℓ`, `ℓ * 3 < Fintype.card V + 3` and `G.HasCycleOfLength ℓ`.
--
--   **Why this is a variation.** This is a variation of the Caccetta–Häggkvist conjecture on the platform (Ten Challenges 03), the open statement that out-degree at least $r$ forces a directed cycle of length at most $\lceil n/r\rceil$. It is the case $r=3$ at its first non-trivial sizes $n\le 9$, in the parent's own definition `CaccettaHaggkvistFor`. Settling it gives the finite base cases for the induction and discharging arguments by which the parent is attacked for small out-degree.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   L. Caccetta and R. Haggkvist, On minimal digraphs with given girth, Congressus Numerantium 21 (1978), 181-187 (cited from memory, not re-checked). The case of out-degree 3 is known in the literature on the conjecture (Hamidoune and others, cited from memory); this statement is its restriction to at most 9 vertices, which was verified by a SAT solver: no digraph on 7, 8 or 9 vertices with minimum out-degree 3 avoids directed cycles of lengths 2 and 3, while on 10 vertices one exists (the limit of the argument). For at most 6 vertices a 2-cycle follows from counting arcs. Origin: the platform problem TenChallenges.challenge_03 (Caccetta-Haggkvist conjecture, Open).

import Definitions.Def_TenChallenges_CaccettaHaggkvist

set_option autoImplicit false

namespace LefebvreVariations

/-- The Caccetta–Häggkvist conjecture at minimum out-degree `r = 3`, restricted to digraphs
with at most `9` vertices: a loopless digraph on `n ≤ 9` vertices with every out-degree at
least `3` has a directed cycle of length `ℓ` with `ℓ * 3 < n + 3`, that is of length at most
`⌈n/3⌉` (length `2` when `n ≤ 6`, length at most `3` for `7 ≤ n ≤ 9`). The conclusion is
the parent's `CaccettaHaggkvistFor 3`, verbatim. For `n = 10` the bound `⌈10/3⌉ = 4`
leaves room: there is a `10`-vertex digraph of minimum out-degree `3` with no cycle of length
`2` or `3`, so `9` is the largest `n` where only `ℓ ≤ 3` is needed. Both facts were checked
with a SAT solver while preparing this statement.
Source: Caccetta and Häggkvist, "On minimal digraphs with given girth", Congressus Numerantium
21 (1978), 181-187; the conjecture is known for small `r` (Hamidoune, Shen and others; cited from memory). -/
theorem caccetta_haggkvist_three_card_le_nine
    {V : Type} [Fintype V] [Nonempty V] (hcard : Fintype.card V ≤ 9) (G : Digraph V)
    (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, 3 ≤ G.outDegree v) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * 3 < Fintype.card V + 3 ∧ G.HasCycleOfLength ℓ := by
  sorry

end LefebvreVariations

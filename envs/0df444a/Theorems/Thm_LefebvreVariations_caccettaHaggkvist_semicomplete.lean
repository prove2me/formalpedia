-- Prove2me | Theorems.Thm_LefebvreVariations_caccettaHaggkvist_semicomplete
-- name    : LefebvreVariations.caccettaHaggkvist_semicomplete
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:43:09.697877+00:00
-- url     : https://prove2.me/theorems/7affcb12-49b0-42f9-91b0-7961b26d65db
-- title:
--   Lefebvre's variations, No. 27 — on a theme by Caccetta and Häggkvist: the Caccetta–Häggkvist bound for semicomplete digraphs
-- statement:
--   This is the Caccetta–Häggkvist conjecture for semicomplete digraphs, in particular for tournaments.
--
--   Let $D$ be a loopless digraph on $n$ vertices with minimum out-degree $r\ge1$ in which every two distinct vertices are joined by at least one arc. Then $D$ has a directed cycle of length $\ell\ge2$ with
--
--   $$
--   \ell\,r<n+r,\qquad\text{that is,}\qquad \ell\le\Big\lceil\frac nr\Big\rceil .
--   $$
--
--   If two vertices are joined in both directions there is a $2$-cycle. Otherwise $D$ is a tournament: some vertex has in-degree at least $r$, which forces $n\ge2r+1$, and a tournament with minimum out-degree at least $1$ contains a directed triangle (take a vertex of minimum out-degree), so $\ell=3$ satisfies $3r<n+r$.
--
--   The Caccetta–Häggkvist conjecture asserts the same bound for all loopless digraphs; dense digraphs are the classical easy regime, and semicomplete digraphs are the extreme case where it holds with cycles of length at most three.
--
--   **Formalization Note** Digraphs, out-degree and cycles are the mission's definitions; the hypothesis says that for distinct $u,v$ there is an arc $u\to v$ or $v\to u$.
--
--   **Why this is a variation.** This varies the Caccetta–Häggkvist conjecture, which asks for a directed cycle of length at most $\lceil n/r\rceil$ in every digraph on $n$ vertices with minimum out-degree $r$. It is the special case of semicomplete digraphs (any two vertices joined by an arc in at least one direction, tournaments included), where the conjecture holds for every $r$. Settling it removes a whole class of digraphs from the search for a counterexample to the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Conjecture: L. Caccetta and R. Häggkvist, On minimal digraphs with given girth, Congr. Numer. 21 (1978), 181–187. Directed triangles in tournaments: J. W. Moon, Topics on Tournaments, Holt, Rinehart and Winston, 1968 (a tournament without a directed 3-cycle is transitive). Parent problem: TenChallenges.challenge_03 (Caccetta–Häggkvist conjecture).

import Mathlib
import Definitions.Def_TenChallenges_CaccettaHaggkvist

namespace LefebvreVariations

/-- The Caccetta-Häggkvist conjecture (Challenge 03) for semicomplete digraphs (every two
distinct vertices are joined by an arc in at least one direction; tournaments are the
oriented case): minimum out-degree `r ≥ 1` on `n` vertices gives a directed cycle of
length `ℓ` with `ℓ r < n + r`, i.e. `ℓ ≤ ⌈n / r⌉`. A digon gives `ℓ = 2` (as `n > r`); without
a digon the arc count forces `n ≥ 2r + 1` and a vertex of least out-degree lies on a
directed triangle (an acyclic-of-triangles tournament is transitive, so has a sink),
and `3 r < n + r`.
Source: Caccetta and Häggkvist, "On minimal digraphs with given girth", Congr. Numer. 21
(1978), 181-187 (the conjecture); for tournaments the triangle comes from Moon,
*Topics on Tournaments*, Holt, Rinehart and Winston 1968, Section 1 (a tournament without
a directed 3-cycle is transitive; Camion 1959). -/
theorem caccettaHaggkvist_semicomplete (r : ℕ) (hr : 0 < r) {V : Type} [Fintype V]
    [Nonempty V] (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v)
    (hsemi : ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u)
    (hdeg : ∀ v, r ≤ G.outDegree v) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * r < Fintype.card V + r ∧ G.HasCycleOfLength ℓ := by
  sorry

end LefebvreVariations

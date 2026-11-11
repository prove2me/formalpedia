-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_proposition_23
-- name    : FullImmersionFPT.Main.proposition_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:48:53.425643+00:00
-- url     : https://prove2.me/theorems/8d22371b-3a1a-4621-89ab-d45433c7bb6c
-- title:
--   Proposition 23 — improve a dictionary or find a respecting certificate in O(m³) time
-- statement:
--   Let $(G,\Sigma,t)$ be a signed graph with $m=|E(G)|$ edges and $D$ a dictionary: a non-empty set of floodings of equal value whose size is at most one plus the number of candidates (up to equivalence) it displays. Then one can find, in time
--   $$O(|E(G)|^3),$$
--   either a dictionary $D'$ which improves $D$ (greater value, or equal value and more displayed candidates), or a certificate $(X,\Sigma')$ which respects $D$ (it has the value of $D$ and every edge it does not force is displayed by $D$). Formally: one program $P$, a factor $b$ and a constant $c$ with $P$ halting within $c\,m^3+c$ steps on every signed graph and dictionary. Repeating it at most $2|E(G)|$ times yields Theorem 3 for signed graphs.
--
--   Differences from the source:
--   - reading: "we can find/compute/test … in time O(|E(G)|³)" → one program P of the published TrulySubcubicAPSP word RAM and a word-size factor b, fixed before every input; on every input and every word size W ≥ b(⌊log₂(N+2)⌋+1) (FOMCMonDep.WordSizeOK, N = input length plus largest absolute entry) P halts within the explicit bound with a correct output; reason: the paper fixes a RAM storing graphs as adjacency lists of half-edges with constant-time access (p. 15) but names no formal machine; unit-cost word RAM with logarithmic words is the reading; each O(·) is an explicit constant chosen after the parameters it is subscripted with
--   - reading: D′ "displays more candidates" → D′ displays strictly more candidate classes (up to equivalence) than D; reason: a count, as in the size bound of a dictionary and in the progress argument
--   - encoding: a dictionary, a set of floodings → a list of pairwise inequivalent floodings (equivalence: same circuits up to reversal and order), written as dictWords; reason: floodings differing by reversals are the same (p. 14)
--   - encoding: a graph given to the algorithm → an edge list on Fin n with half-edges (e, i) : Fin m × Fin 2 (inc (e, i) = ends e i, mate (e, i) = (e, 1 − i)) written as words (FreeCode.words, DecoCode.words); outputs are words in the cells after the input (RunsWithin, FOMCMonDep.Emits); reason: every finite multigraph with loops and parallel edges is isomorphic to such an edge list, and every edge order and orientation is allowed
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
--   - encoding: value(X, Σ′) = |E_{F,Σ′}(X)| + |δ(X)|/2 − odd_{Σ′}(G − X) → certValue in ℤ with (|δ(X)| : ℤ) / 2; reason: |δ(X)| is even in an Eulerian graph, so the division is exact; ℤ avoids truncated subtraction
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 26, Proposition 23

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Flooding

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Proposition 23** (p. 26). There are a program `P`, a factor `b` and a constant `c` such that,
given a signed graph `(G, Σ, t)` with `m` edges and a dictionary `D`, `P` finds within `c · m³ + c`
steps either a dictionary `D′` which improves `D`, or a certificate `(X, Σ′)` which respects `D`. -/
theorem proposition_23 :
    ∃ (P : List TrulySubcubicAPSP.Instr) (b c : ℕ),
      ∀ (n m : ℕ) (Φ : FreeCode n m) (D : List (List (List (Fin m × Fin 2)))),
        Φ.toFree.IsSigned → Φ.toFree.IsDictionary D → ∀ W : ℕ,
        FOMCMonDep.WordSizeOK b (Φ.words ++ dictWords D) W →
        RunsWithin P W (c * m ^ 3 + c) (Φ.words ++ dictWords D) fun out =>
          (∃ D', Φ.toFree.IsDictionary D' ∧ Φ.toFree.Improves D' D ∧
              FOMCMonDep.Emits out (0 :: dictWords D')) ∨
            ∃ X S', Φ.toFree.IsCertificate X S' ∧ Φ.toFree.Respects X S' D ∧
              FOMCMonDep.Emits out (1 :: certWords X S') := by sorry

end FullImmersionFPT.Main

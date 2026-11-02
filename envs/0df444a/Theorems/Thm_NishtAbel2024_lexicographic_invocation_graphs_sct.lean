-- Prove2me | Theorems.Thm_NishtAbel2024_lexicographic_invocation_graphs_sct
-- name    : NishtAbel2024.lexicographic_invocation_graphs_sct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T02:29:48.667256+00:00
-- url     : https://prove2.me/theorems/cfeab656-6660-4984-8a71-9b030278260e
-- title:
--   Lexicographic invocation graphs satisfy size-change termination
-- statement:
--   Let $D$ be a finite list of function names, $n$ a common parameter arity, and $m$ a duplicate-free list of parameter indices less than $n$. At each position $k$ of $m$, form the invocation graph with a strict diagonal edge at $m_k$, non-strict diagonal edges at earlier measure positions, and no other edges. Assign this family to every pair of names in $D$. Then the resulting family is well formed and satisfies the size-change termination criterion: every idempotent cycle graph in its compositional closure has a strict diagonal edge.
--
--   This is the invocation-graph construction used in the proof of Theorem 6, Section 5.5, pp. 39–40. The formulation also permits an empty measure, for which every graph list and the compositional closure are empty. It proves the graph obligation; it does not assert a translation from an independently defined source typing system.
-- source:
--   K. Nisht, Type-Based Termination Checking in Agda (2024), Section 5.5, proof of Theorem 6 and Figure 3, pp. 39–40, https://knisht.github.io/agda/msc.pdf

import Definitions.Def_NishtAbel2024_Syntax

namespace NishtAbel2024

theorem lexicographic_invocation_graphs_sct :
    ∀ (dom : List FunName) (n : Nat) (m : List Nat),
      m.Nodup → (∀ i ∈ m, i < n) → SCTValid (lexInvGraphFamily dom n m) := by sorry

end NishtAbel2024

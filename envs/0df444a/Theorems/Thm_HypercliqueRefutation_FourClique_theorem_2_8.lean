-- Prove2me | Theorems.Thm_HypercliqueRefutation_FourClique_theorem_2_8
-- name    : HypercliqueRefutation.FourClique.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:11.127295+00:00
-- url     : https://prove2.me/theorems/8bb4efaf-d1b3-4aad-9039-b265b243b0bb
-- title:
--   Theorem 2.8 — deterministic counting and finding in O(n^3.957)
-- statement:
--   There is a uniform deterministic word-RAM algorithm on every finite 3-uniform hypergraph G on n vertices with
--
--   $$T(n)=O(n^{3957/1000}).$$
--
--   Given n and the dense Boolean triple indicator, it returns the exact number of unordered four-hypercliques and returns a valid four-vertex clique exactly when that number is positive. Its acceptance verdict agrees with positivity. When the number is zero, it returns a zero count, a none tag and zero inactive label cells. There are no promises on G or on n and no fast solver or precomputed coefficient data in the input.
--
--   The precise machine statement is the published SolvedInTime predicate for the count-and-witness problem. For every input-magnitude exponent κ, a single finite program and uniform time bound are chosen before n, G and the physical word width. Correctness holds at every sufficiently large word width proportional to log n. The universal κ=0 case already covers all Boolean hypergraph inputs, so the output guarantee is not vacuous on any graph.
--
--   This is the full explicit-exponent target from the paper with the counting/reporting output made explicit; the supporting operational results are proof obligations, not hypotheses.
--
--   Differences from the source:
--   - generalization: the four-hyperclique problem can be solved, with counting and logarithmic-factor reporting discussed in Section 2.1 → exact unordered count and an actual witness or absence output at exponent 3957/1000; reason: the source supplies counting and binary-search reporting and the strict exponent slack is intended to absorb the logarithmic witness overhead; this is an open proof obligation, not an assumed solver
--   - reading: deterministic time without an explicit instruction set → the published finite-program word RAM and uniform SolvedInTime semantics; reason: the brief selects this machine reading, with charged add/subtract/multiply, memory operations and branches; the machine implementation and bit-growth bridge remain to be proved
--   - encoding: n vertices, hyperedges and decimal exponent 3.957 → Fin n vertices, n³ Boolean triple entries, and the exact rational exponent 3957/1000; reason: all finite hypergraphs are admitted; repeated triples are zero, and κ=0 covers every graph, including n=0
--   - encoding: report one clique if it exists, otherwise no clique → six output cells: count, 0/1 tag and four labels; inactive labels are zero; reason: a canonical finite output convention imposes no restriction on input graphs and makes absence output explicit
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026), held source.pdf SHA-256 fda90f18867fd07883366a1bc49a8afa652b8712f71402e11ccd45e6633b127a; Theorem 2.8, p.6; Section 2.1 first paragraph and Problem 2.1, p.3; graph setting in Section 1, p.1.

import Mathlib
import Definitions.Def_HypercliqueRefutation_FourClique_CountWitness

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique

/-- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
    Theorem 2.8, p.6; count and witness semantics from Section 2.1, p.3.
    The exact rational exponent is 3957/1000. There are no instance hypotheses,
    multiplication oracle, coefficient certificate or fast-solver assumptions. -/
theorem theorem_2_8 :
    countWitnessProblem.SolvedInTime (3957 / 1000 : ℚ) := by sorry

end HypercliqueRefutation.FourClique

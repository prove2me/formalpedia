-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_inDegree_univ_eq_five
-- name    : MultipleUnicast.Counterexample.inDegree_univ_eq_five
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:18:17.886562+00:00
-- url     : https://prove2.me/theorems/b895bad8-706e-4833-874e-80eae67031dd
-- title:
--   §4 — every vertex has in-degree 5 in the full candidate orientation
-- statement:
--   Orient each of the 910 candidate edges of the point–line incidence graph of $PG(2,9)$ from its earlier to its later endpoint in the processing order $\pi$ when the edge is kept, and from later to earlier when it is one of the 175 deleted edges (`head`, `tail`). Then every one of the 182 vertices is the head of exactly $5$ candidate edges: `inDegree Finset.univ v = 5` for all `v`.
--
--   This is the in-degree half of the displayed identity $d^-(v) = d^+(v) = 5$ of §4 (mission *The Multiple Unicast Conjecture is False*, p. 10: "The displayed finite lists satisfy $d^-(v) = d^+(v) = 5$, $d^+_C(v) = d^-_J(v)$ at every vertex"), one conjunct of `MultipleUnicast.Counterexample.balanced_orientation`, published on its own so that the proof of that milestone splits into pieces that fit the verifier's time limit. All objects are those of the bundle `Def_MultipleUnicast_Counterexample_Graph`.
-- source:
--   The Multiple Unicast Conjecture is False: Causal network coding beats fractional routing (STOC 2027 submission 286), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, p. 10, §4, the in-degree identity d⁻(v) = 5 for the full candidate orientation

import Mathlib
import Definitions.Def_MultipleUnicast_Counterexample_Graph

namespace MultipleUnicast.Counterexample

theorem inDegree_univ_eq_five :
    ∀ v : Vertex, inDegree Finset.univ v = 5 := by
  sorry

end MultipleUnicast.Counterexample

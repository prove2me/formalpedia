-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_theorem_3_7
-- name    : KColoringFaster.ListBootstrap.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:44.061982+00:00
-- url     : https://prove2.me/theorems/90d35dbf-b509-490e-a0b0-840d1ac8804b
-- title:
--   Theorem 3.7 — two-block restricted coloring
-- statement:
--   Let $P=Q\,\dot\cup\,R$ be an arbitrary finite palette of natural numbers, and let $V_c\subseteq V(G)$ be the allowed domain of each color $c\in P$ in a graph $G$ on $n$ vertices. Define
--   $$D_Q=\bigcup_{c\in Q}V_c,\qquad D_R=\bigcup_{c\in R}V_c.$$
--   Whether $G$ admits a proper coloring $\varphi:V(G)\to P$ in which every color $c$ is used only on $V_c$ can be decided in
--   $$O^*\big(2^{|D_Q|}+2^{|D_R|}\big)$$
--   time, with one-sided error at most $e^{-n}$.
--
--   This is the "stitching" step of the general algorithm. The paper assembles it from Lemmas 3.11, 3.14, 3.16 and Observation 3.23 of Zamir, *Algorithmic applications of hypergraph and partition containers*, STOC 2023, and gives no proof of its own.
--
--   **Formalization Note** Instances are encoded as in the definition `TwoBlock`; algorithms and $O^*$ are as in `Algorithms`.
--
--   Differences from the source:
--   - reading: "can be decided" → decided with one-sided error at most $e^{-n}$; reason: §3 (p. 7) allows exponentially small error for all algorithms and says errors can be taken one-sided
--   - encoding: "and exponential space" → space not bounded separately; reason: a run of cost $B$ touches at most $B$ memory cells, so the time bound already bounds the space
--   - encoding: $O^*(\cdot)$ time → one program and polynomials $p,q$ fixed before the input, worst-case cost $\lceil p(\sigma)\,T\rceil$ on the integer RAM with registers of at most $q(\sigma)$ bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: arbitrary palette → finite set of natural numbers; reason: any finite palette is numbered
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 11, Theorem 3.7 (assembled from Zamir, STOC 2023, Lemmas 3.11, 3.14, 3.16, Observation 3.23, as described on p. 10)

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms
import Definitions.Def_KColoringFaster_ListBootstrap_TwoBlock

open Classical

namespace KColoringFaster.ListBootstrap

/-- Theorem 3.7 (Two-block restricted coloring), p. 11. Let `P = Q ∪̇ R` be an arbitrary palette and
`V c ⊆ V(G)` the allowed domain of each color `c ∈ P`; put `D_Q = ⋃_{c ∈ Q} V c` and
`D_R = ⋃_{c ∈ R} V c`. Whether `G` has a proper coloring with colors in `P` in which every color `c`
is used only on `V c` is decided in `O*(2^{|D_Q|} + 2^{|D_R|})` time, with one-sided error at most
`e^{-n}`. -/
theorem theorem_3_7 :
    RandDecides encTwoBlock TwoBlockInstance.n (fun _ => True) TwoBlockInstance.Yes
      (fun I => (2 : ℝ) ^ I.DQ.card + (2 : ℝ) ^ I.DR.card) (expErr 1) zeroErr := by sorry

end KColoringFaster.ListBootstrap

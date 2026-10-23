-- Prove2me | Theorems.Thm_LPCommunity_LPRecovery_theorem_4
-- name    : LPCommunity.LPRecovery.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:48.196068+00:00
-- url     : https://prove2.me/theorems/bee5aa7f-4c7a-4876-8e97-8a2e7e8c367e
-- title:
--   Theorem 4, p. 12 — regular sandwiching with d_in − d_out ≥ n/4 makes the metric LP recover the planted bisection
-- statement:
--   Let $G$ be a graph on $V=\{1,\dots,n\}$ with planted bisection $V_1,V_2$, induced subgraphs $G_1=G[V_1]$, $G_2=G[V_2]$, and crossing graph $G_0$. Let $d_{\mathrm{in}},d_{\mathrm{out}}$ be nonnegative integers and assume that
--
--   1. $G_1$ and $G_2$ contain $d_{\mathrm{in}}$-regular subgraphs on the same node sets $V_1$ and $V_2$;
--   2. $G_0$ is a subgraph of a $d_{\mathrm{out}}$-regular bipartite graph with the same bipartition $V_1,V_2$.
--
--   If
--   $$d_{\mathrm{in}}-d_{\mathrm{out}}\ \ge\ \frac n4,$$
--   then the metric relaxation (LP-P) recovers the planted bisection: the cut vector of $V_1,V_2$ is its unique optimal solution.
--
--   This extends the regular-graph criterion (Proposition 2) to irregular graphs that can be sandwiched between regular ones; the paper's analysis of the very dense stochastic block model (Theorem 6) applies it to random graphs, for which such sandwiching holds with high probability.
--
--   **Formalization Note** The two spanning $d_{\mathrm{in}}$-regular subgraphs of $G_1$ and $G_2$ are represented by one graph $H_1$ that has no crossing edges, all of whose edges are edges of $G$, and in which every vertex has $d_{\mathrm{in}}$ neighbours on its own side; the $d_{\mathrm{out}}$-regular bipartite supergraph is a graph $H_0$ with only crossing edges, containing every crossing edge of $G$, in which every vertex has $d_{\mathrm{out}}$ neighbours. On p. 12 the paper names $d_{\mathrm{in}}$ and $d_{\mathrm{out}}$ the minimum and maximum degrees of $G_1\cup G_2$ and $G_0$, but the proof works for any integers satisfying the sandwich hypotheses, and Theorem 6's proof (p. 15) applies Theorem 4 with other integers; the theorem is therefore posed for arbitrary $d_{\mathrm{in}},d_{\mathrm{out}}$, which contains the literal reading as the special case $d_{\mathrm{in}}=$ minimum inside degree, $d_{\mathrm{out}}=$ maximum outside degree. No range hypotheses on $n$, $d_{\mathrm{in}}$, $d_{\mathrm{out}}$ are added; they are implied by the hypotheses (or the statement is trivial at $n=0$). All comparisons are in $\mathbb R$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 12, Theorem 4

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting

open Finset
open scoped Classical

namespace LPCommunity.LPRecovery

theorem theorem_4 {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (din dout : ℕ)
    (h1 : ∃ H : SimpleGraph (Fin n), (∀ i j, H.Adj i j → LPCommunity.MinBisect.sameSide V1 i j ∧ G.Adj i j) ∧
      ∀ v, LPCommunity.MinBisect.inDeg H V1 v = din)
    (h0 : ∃ H : SimpleGraph (Fin n), (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
      (∀ i j, G.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j → H.Adj i j) ∧ ∀ v, LPCommunity.MinBisect.outDeg H V1 v = dout)
    (h : (din : ℝ) - dout ≥ (n : ℝ) / 4) :
    LPRecovers G V1 := by sorry

end LPCommunity.LPRecovery

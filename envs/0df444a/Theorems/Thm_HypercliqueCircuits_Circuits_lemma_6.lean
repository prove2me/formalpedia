-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_6
-- name    : HypercliqueCircuits.Circuits.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:39.985121+00:00
-- url     : https://prove2.me/theorems/09614fb3-b414-4e25-aaff-c8e3c3fd9c96
-- title:
--   Lemma 6 — support-graph edge count
-- statement:
--   Let $0<\epsilon\le1/8$, $B\ge16$ and $(eB)^2\le2^{\epsilon B}$. For every $d\ge0$, put $q=2^B$, $n=q^d$ and $t=\lfloor d/B\rfloor$. The graph has left labels with $a(\sigma)\ge d-t$, right rows $i\in[q]^d$, and an edge exactly when row $i$ of $E_\sigma$ is nonzero. Then
--
--   $$|E(G)|\le n^{2+\epsilon/(2B)}.$$
--
--   The prefactor is exactly one, as in the displayed final estimate of the proof. No edge-count hypothesis is placed on the graph. This controls the actual amount of support to be partitioned.
--
--   Differences from the source:
--   - encoding: O(n^(2+epsilon/(2B))) in the lemma, with explicit prefactor one in its proof → the proof inequality with prefactor one for every d; reason: retains the quantitative constant supplied on the same page
--   - generalization: graph analyzed within the inductive circuit section → the graph bound without an inductive circuit premise; reason: the graph and the counting proof depend only on B,d and admissibility
--   - encoding: q=2^B, n=q^d, t=floor(d/B) → rows indexed directly by q-ary digit vectors; reason: digit-vector indices have exactly q^d values; d=0 gives the singleton instance n=1
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 6 and its proof, p.20 (PDF 21).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 6, printed p.20 / PDF 21; the proof gives prefactor one. -/
theorem lemma_6 (ε : ℝ) (B : ℕ) (hB : Admissible ε B) (d : ℕ) :
    ((supportEdges B d).card : ℝ) ≤ (((2^B)^d : ℕ) : ℝ) ^ (2+ε/(2*B)) := by sorry

end HypercliqueCircuits.Circuits

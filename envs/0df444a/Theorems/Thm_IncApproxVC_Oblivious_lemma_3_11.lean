-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_3_11
-- name    : IncApproxVC.Oblivious.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:27.381683+00:00
-- url     : https://prove2.me/theorems/9477f9ce-e476-435a-9293-901157f83471
-- title:
--   Lemma 3.11 — with $\alpha=\varepsilon k/\nu$ and $F^*=(1+\varepsilon)k$, threshold $\alpha$-penalty cut solves the local edge cut problem
-- statement:
--   Let $G$ be a simple directed graph with $m$ edges, $s$ a vertex, $k\ge 1$ an integer, $\nu>0$ and $0<\varepsilon<1$ with $2\nu<\varepsilon m$ (the parameters of the Local Edge Cut Problem, Definition 3.5). Put
--   $$\alpha=\frac{\varepsilon k}{\nu},\qquad F^*=(1+\varepsilon)k .$$
--   Then (i) every $s$-rooted edge cut $(S,V\setminus S)$ with $|\partial^+(S)|\le k$ and $\mathrm{vol}^+(S)\le\nu$ has $\alpha$-penalty score at most $F^*$; and (ii) every set $S\ni s$ with score at most $F^*$ gives an edge cut $(S,V\setminus S)$ (in particular $S\ne V$) with $|\partial^+(S)|\le(1+\varepsilon)k$ and $\mathrm{vol}^+(S)\le 2\nu/\varepsilon$. Hence an algorithm for threshold $\alpha$-penalty cut answers the (incremental) local edge cut problem: NO certifies that no small cut of volume $\le\nu$ exists, and YES certifies a cut of size $\le(1+\varepsilon)k$ and volume $\le 2\nu/\varepsilon$.
--
--   Differences from the source:
--   - reading: The incremental local edge cut problem can be solved by running an algorithm for threshold α-penalty cut with α = εk/ν and F* = (1+ε)k → the two implications (i), (ii) of its proof, for every graph, under Definition 3.5's 0 < ε < 1 and 2ν < εm; reason: the lemma's mathematical content; an incremental instance is a sequence of such graphs
--   - reading: parameters k, ν of Definition 3.5 → k a natural number ≥ 1 and ν > 0; reason: threshold α-penalty cut needs α, F* > 0 (Definition 3.9), i.e. k, ν > 0; k is a cut size
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 8, Lemma 3.11 (with Definition 3.5, p. 6)

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_Cuts

namespace IncApproxVC.Oblivious

/-- **Lemma 3.11**, p. 8, stated as the two implications of its proof. Let `G` be a simple graph
with `m` edges, `s` a vertex, `k ≥ 1`, `ν > 0` and `0 < ε < 1` with `2ν < εm` (Definition 3.5), and
put `α = εk/ν`, `F* = (1 + ε)k`. (i) Every `s`-rooted edge cut `(S, V \ S)` with `|∂⁺(S)| ≤ k` and
`vol⁺(S) ≤ ν` has `α`-penalty score at most `F*`. (ii) Every `S ∋ s` of score at most `F*` gives an
edge cut `(S, V \ S)` (so `S ≠ V`) with `|∂⁺(S)| ≤ (1 + ε)k` and `vol⁺(S) ≤ 2ν/ε`. -/
theorem lemma_3_11 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (s : V) (k : ℕ) (hk : 1 ≤ k) (ν ε : ℝ) (hν : 0 < ν) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hm : 2 * ν < ε * (G.numEdges : ℝ)) :
    (∀ S : Finset V, s ∈ S → Digraph.IsEdgeCut S Sᶜ → (G.outBoundary S).card ≤ k →
        (G.vol S : ℝ) ≤ ν → G.penaltyScore (ε * k / ν) S ≤ (1 + ε) * k) ∧
      (∀ S : Finset V, s ∈ S → G.penaltyScore (ε * k / ν) S ≤ (1 + ε) * k →
        Digraph.IsEdgeCut S Sᶜ ∧ ((G.outBoundary S).card : ℝ) ≤ (1 + ε) * k ∧
          (G.vol S : ℝ) ≤ 2 * ν / ε) := by sorry

end IncApproxVC.Oblivious

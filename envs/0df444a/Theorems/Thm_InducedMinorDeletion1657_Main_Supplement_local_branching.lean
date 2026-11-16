-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_Supplement_local_branching
-- name    : InducedMinorDeletion1657.Main.Supplement.local_branching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:15:54.92721+00:00
-- url     : https://prove2.me/theorems/dda8a898-a6ed-4bca-93c1-f9c3b147e014
-- title:
--   Lemma 7.1 — local branching with balanced induced subgraphs
-- statement:
--   Fix a finite graph $H$ and a positive integer $t$. There are positive real constants $c_1,c_2,c_3$ and positive natural exponents $e,w$, depending only on $H,t$, such that for every $0<\delta\le1/2$ there are a threshold $q_0\ge2$ and one deterministic RAM program. For every $q\ge q_0$, every $H$-induced-minor-free graph $G$ on $n$ vertices, and every set $W$ of size $q$, it outputs a list of at most
--   $$2^{c_2\delta^{-3}(\log_2q)^9}$$
--   quadruples $(Y,Z,A_1,A_2)$. Every entry has $Z\cap Y=\varnothing$, and $A_1,A_2$ are disjoint, anticomplete, and partition $V(G)\setminus(Y\cup Z)$. For $j=1,2$,
--   $$|W\cap A_j|\le 2q/3,\qquad |Z|\le c_1q/(\log_2q)^3,\qquad \operatorname{tw}(G[A_j])\le c_3q/(\log_2q)^4.$$
--   Every treewidth-$t$ modulator $S$ with $|S|\le q/\delta$ contains the $Y$ of some entry. The program is given only $G,W$ and halts with the encoded list in at most
--   $$2^{c_2\delta^{-3}(\log_2q)^9}(n+1)^e$$
--   word operations, charging output length and satisfying the base word-size bound with exponent $w$. All structural constants and exponents precede $\delta$; only the threshold and program may depend on $\delta$. This is the full local-branching interface needed for Theorem 1.2.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; reason: finite relabeling preserves every instance; the base nonnegative treewidth convention changes no nonnegative-width predicate
--   - reading: a family of size 2^{c2 δ^{-3} log^9 q} → an upper bound on list length; reason: the proof explicitly says its cardinality is at most; duplicate entries can be removed
--   - encoding: log q with no base and sufficiently large q → log₂ q and an existential threshold q0 at least 2; reason: changing a fixed logarithm base rescales the uniform constants; the threshold excludes undefined logarithmic denominators
--   - encoding: family Y with associated Z and two induced subgraphs → a list of vertex-set quadruples partitioning the residual vertices, with no cross edges; reason: the induced subgraphs are determined by their vertex sets and all five source clauses are retained
--   - encoding: algorithm in exponential-factor times n^{O(1)} time → one base RAM program on graph/W encodings, bounded live words and charged output, with a uniform polynomial exponent and n+1; reason: actual execution replaces an informal algorithm; the fixed polynomial overhead and small input convention are absorbed in constants
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 29 (PDF p. 30), Lemma 7.1; proof printed 30 / PDF 31

import Definitions.Def_InducedMinorDeletion1657_Main_Supplement_LocalBranching

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main.Supplement

/-- Lemma 7.1, printed p.29 / PDF p.30. Structural constants and polynomial
exponent are independent of δ; one operational program precedes every instance. -/
theorem local_branching :
  ∀ (H : InputGraph) (t : ℕ), 0 < t →
    ∃ (c₁ c₂ c₃ : ℝ) (e wordBound : ℕ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < e ∧ 0 < wordBound ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
        ∃ (q₀ : ℕ) (P : Program), 2 ≤ q₀ ∧
          ∀ (q : ℕ), q₀ ≤ q → ∀ (G : InputGraph) (W : Finset (Fin G.n)),
            excluded H.graph G.graph → W.card = q →
            ∃ L : List (LocalEntry G.n),
              (L.length : ℝ) ≤ localCount c₂ δ q ∧
              localResult G W q t δ c₁ c₃ L ∧
              ramOutputs P (localInput G W) (localWords L)
                (localCount c₂ δ q * ((G.n : ℝ) + 1) ^ e) wordBound := by sorry

end InducedMinorDeletion1657.Main.Supplement

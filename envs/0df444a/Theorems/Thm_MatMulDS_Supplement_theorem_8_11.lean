-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_11
-- name    : MatMulDS.Supplement.theorem_8_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:20:16.683883+00:00
-- url     : https://prove2.me/theorems/24d46c05-8f25-4106-9043-6c3b816bc502
-- title:
--   Theorem 8.11 — exact distances from $S$ with $m\le n^{3/2}$ in $O(n^{2-\xi})$ w.h.p., $\xi=3\beta/10-\beta^2$
-- statement:
--   Let $\beta\le1/50$ be an admissible saving, and set $\xi=3\beta/10-\beta^2$. Using the bounds (3.3) of [Uzn26], there is a randomized algorithm that, given an undirected unweighted graph $G=(V,E)$ with $n\ge2$ vertices and $m\le n^{3/2}$ edges and a set $S\subseteq V$, always returns $d_G(s,v)$ for all $(s,v)\in S\times V$, and that runs in
--   $$O(n^{2-\xi})=O(n^{1.9999201})$$
--   time with high probability if $|S|\le\lceil\sqrt n\rceil$.
--
--   For $|S|=\lceil\sqrt n\rceil$ and $m=n^{3/2}$ both classical approaches take quadratic time; this is the first truly subquadratic algorithm in this regime.
--
--   Differences from the source:
--   - encoding: a randomized algorithm on the word RAM → a program of the mission's machine over $\mathbb F_2$, whose coin instruction draws a uniform bit, every step counted, every word size $w\ge K\lceil\log_2(n+1)\rceil+K$; reason: a word RAM with random bits; the field cells over $\mathbb F_2$ are a bit array
--   - reading: "always returns" → every halting run, on every coin sequence, is correct, and the run halts with probability one; reason: a Las Vegas guarantee; "returns" implies halting
--   - reading: "with high probability" → for every $c>0$ a constant $C$ (depending on $c$) with probability at least $1-n^{-c}$; reason: the form the paper's own proofs give (Theorems E.4, E.5, Lemma J.2; SUPPLEMENT decision 1)
--   - reading: "Using the bounds (3.3) of [Uzn26]" → no hypothesis; reason: it names a cited theorem the proof uses; assuming it would weaken the statement (SUPPLEMENT decision 2)
--   - encoding: a graph $G=(V,E)$ with $n$ vertices and $m$ edges → $V=\{0,\dots,n-1\}$, any adjacency-list representation $L$ of $G$ as input words, $m$ the number of edges; reason: the source's input convention (§3: graphs given by adjacency lists)
--   - encoding: output $d_G(s,v)$ on $S\times V$ → word cell $kn+v$ holds $d_G(S_k,v)$, $-1$ for $\infty$; $S$ a list without repetitions; reason: a layout on the machine
--   - encoding: the numerical form $O(n^{1.9999201})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.11, p.57 (PDF p.59); proof via Theorem E.5, p.98

import Mathlib
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_adjWords
import Definitions.Def_MatMulDS_Supplement_coinFrac

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.11, p.57** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let
`β ≤ 1/50` be an admissible saving, and set `ξ = 3β/10 − β²`. Using the bounds (3.3) of [Uzn26], there is a randomized algorithm
that, given an undirected unweighted graph `G = (V, E)` with `n ≥ 2` vertices and `m ≤ n^{3/2}` edges and a set `S ⊆ V`, always
returns `d_G(s, v)` for all `(s, v) ∈ S × V`, and that runs in `O(n^{2−ξ}) = O(n^{1.9999201})` time with high probability if
`|S| ≤ ⌈√n⌉`.

**Formalization Note.**
* A randomized word RAM is a program of the published machine over `𝔽₂` (`coinFrac`), all steps counted, word size
  `w ≥ K⌈log₂(n+1)⌉ + K`. Input words: `adjWords L ++ vtxWords S` for adjacency lists `L` of `G` and a list `S` without
  repetitions. Output: word cell `k n + v` holds `d_G(S_k, v)`, or `−1` for `∞` (`DistTable`).
* "Always returns": every halting run is correct, and the run halts with probability one (`AlwaysReturns`), for every `S`.
* "With high probability": for every `c > 0` there is `C` (depending on `c`) with probability at least `1 − n^{−c}` of halting within
  `C n^{2−ξ}` steps, for `|S| ≤ ⌈√n⌉`.
* "Using the bounds (3.3) of [Uzn26]" names a cited theorem the proof uses; it is not a hypothesis.
* The numerical form is the instance `β = 0.0002666`, stated as the last conjunct. -/
theorem theorem_8_11 (β : ℝ) (hβ : AdmissibleSaving β) (hβ50 : β ≤ 1 / 50) :
    (∃ (P : List AInstr) (K : ℕ),
      (∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L →
        (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) → ∀ S : List (Fin n), S.Nodup →
        ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
          AlwaysReturns P w (adjWords L ++ vtxWords S) (DistTable G S)) ∧
      ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L →
        (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) → ∀ S : List (Fin n), S.Nodup →
        S.length ≤ ⌈Real.sqrt n⌉₊ → ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
          1 - (n : ℝ) ^ (-c) ≤
            coinFrac P w (adjWords L ++ vtxWords S) ⌈C * (n : ℝ) ^ (2 - (3 * β / 10 - β ^ 2))⌉₊ fun _ => True) ∧
    2 - (3 * 0.0002666 / 10 - (0.0002666 : ℝ) ^ 2) ≤ 1.9999201 := by sorry

end MatMulDS.Supplement

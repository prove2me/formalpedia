-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_E_5
-- name    : MatMulDS.Supplement.theorem_E_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:24:56.6732+00:00
-- url     : https://prove2.me/theorems/3e367652-8462-4b79-ad98-ab2be2e91b64
-- title:
--   Theorem E.5 — distances from $2\le|S|\le\lceil\sqrt n\rceil$ sources with threshold $Q$, in $n^{o(1)}(m+T_{\mathrm{small}}+T_{\mathrm{large}}+T_\partial)$ w.h.p.
-- statement:
--   Let $\beta$ be an admissible saving, and fix $0<r<1/2$ and $\delta>0$. Using the bounds (3.3) of [Uzn26], there is a randomized algorithm that, given an undirected unweighted graph $G=(V,E)$ with $n\ge2$ vertices and $m$ edges, a set $S\subseteq V$ with $2\le|S|\le\lceil\sqrt n\rceil$, and a threshold $Q\ge n^{1+\delta}/|S|$, always returns $d_G(s,v)$ for all $(s,v)\in S\times V$ and runs with high probability in time $n^{o(1)}(m+T_{\mathrm{small}}+T_{\mathrm{large}}+T_\partial)$, where
--   $$T_{\mathrm{small}}=n^{1+r}Q^{5/4},\qquad T_{\mathrm{large}}=n^r(n^2+m|S|)\Big(\frac{|S|Q}{n}\Big)^{-2\beta},\qquad T_\partial=n^{2-r+r^2/2}.$$
--
--   Theorem 8.11 is this theorem with a choice of $r$, $Q$ and $\delta$.
--
--   Differences from the source:
--   - encoding: a randomized algorithm on the word RAM → a program of the mission's machine over $\mathbb F_2$, whose coin instruction draws a uniform bit, every step counted, every word size $w\ge K\lceil\log_2(n+1)\rceil+K$; reason: a word RAM with random bits; the field cells over $\mathbb F_2$ are a bit array
--   - reading: "always returns" → every halting run, on every coin sequence, is correct, and the run halts with probability one; reason: a Las Vegas guarantee; "returns" implies halting
--   - reading: "with high probability" → for every $c>0$ a constant $C$ (depending on $c$) with probability at least $1-n^{-c}$; reason: the form the paper's own proofs give (Theorems E.4, E.5, Lemma J.2; SUPPLEMENT decision 1)
--   - reading: "Using the bounds (3.3) of [Uzn26]" → no hypothesis; reason: it names a cited theorem the proof uses; assuming it would weaken the statement (SUPPLEMENT decision 2)
--   - encoding: a graph $G=(V,E)$ with $n$ vertices and $m$ edges → $V=\{0,\dots,n-1\}$, any adjacency-list representation $L$ of $G$ as input words, $m$ the number of edges; reason: the source's input convention (§3: graphs given by adjacency lists)
--   - encoding: a real threshold $Q$ → $Q$ a natural number (an input word); word size $w\ge K\lceil\log_2(n+Q+1)\rceil+K$; reason: a real $Q$ is reduced to $\lceil Q\rceil$, which satisfies the same hypothesis and changes the bound by at most a factor $2^{5/4}$
--   - reading: $n^{o(1)}$ with $o(1)$ depending on $\beta,r,\delta$ → one program, and for every $\eta>0$ (and $c$) a constant $C$ with $Cn^\eta(\cdots)$; reason: the meaning of $n^{o(1)}$ for one algorithm
--   - encoding: output → `DistTable` as in Theorem 8.11; $S$ a list without repetitions; reason: a layout
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem E.5, p.98 (PDF p.100)

import Mathlib
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_adjWords
import Definitions.Def_MatMulDS_Supplement_coinFrac

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem E.5, p.98** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `β` be an
admissible saving, and fix `0 < r < 1/2` and `δ > 0`. Using the bounds (3.3) of [Uzn26], there is a randomized algorithm that, given
an undirected unweighted graph `G = (V, E)` with `n ≥ 2` vertices and `m` edges, a set `S ⊆ V` with `2 ≤ |S| ≤ ⌈√n⌉`, and a threshold
`Q ≥ n^{1+δ}/|S|`, always returns `d_G(s, v)` for all `(s, v) ∈ S × V` and runs with high probability in time
`n^{o(1)}(m + T_small + T_large + T_∂)`, where `T_small = n^{1+r} Q^{5/4}`, `T_large = n^r (n² + m|S|)(|S|Q/n)^{−2β}` and
`T_∂ = n^{2−r+r²/2}`.

**Formalization Note.**
* Randomized word RAM over `𝔽₂` (`coinFrac`), all steps counted. Input words `adjWords L ++ vtxWords S ++ [Q]`; the word size is
  `w ≥ K⌈log₂(n + Q + 1)⌉ + K`. Output as in Theorem 8.11 (`DistTable`).
* The threshold `Q` is a natural number: the algorithm compares it with sizes of neighbourhoods, and a real threshold `Q` can be
  replaced by `⌈Q⌉`, which satisfies the same hypothesis and changes the time bound by at most a factor `2^{5/4}`.
* `n^{o(1)}`: for every `η > 0` some `C` with `C n^η`, depending on `η` (and `β, r, δ`, and `c` of "with high probability"), for the
  one program fixed before `η`; "always returns" and "with high probability" as in Theorem 8.11. -/
theorem theorem_E_5 (β : ℝ) (hβ : AdmissibleSaving β) (r δ : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) (hδ : 0 < δ) :
    ∃ (P : List AInstr) (K : ℕ),
      (∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L →
        ∀ S : List (Fin n), S.Nodup → 2 ≤ S.length → S.length ≤ ⌈Real.sqrt n⌉₊ →
        ∀ Q : ℕ, (n : ℝ) ^ (1 + δ) / S.length ≤ Q →
        ∀ w : ℕ, K * Nat.clog 2 (n + Q + 1) + K ≤ w →
          AlwaysReturns P w (adjWords L ++ vtxWords S ++ [(Q : ℤ)]) (DistTable G S)) ∧
      ∀ c η : ℝ, 0 < c → 0 < η → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G L →
        ∀ S : List (Fin n), S.Nodup → 2 ≤ S.length → S.length ≤ ⌈Real.sqrt n⌉₊ →
        ∀ Q : ℕ, (n : ℝ) ^ (1 + δ) / S.length ≤ Q →
        ∀ w : ℕ, K * Nat.clog 2 (n + Q + 1) + K ≤ w →
          1 - (n : ℝ) ^ (-c) ≤
            coinFrac P w (adjWords L ++ vtxWords S ++ [(Q : ℤ)])
              ⌈C * (n : ℝ) ^ η *
                ((G.edgeSet.ncard : ℝ) + (n : ℝ) ^ (1 + r) * (Q : ℝ) ^ ((5 : ℝ) / 4) +
                  (n : ℝ) ^ r * ((n : ℝ) ^ 2 + G.edgeSet.ncard * S.length) *
                    ((S.length : ℝ) * Q / n) ^ (-2 * β) +
                  (n : ℝ) ^ (2 - r + r ^ 2 / 2))⌉₊ fun _ => True := by sorry

end MatMulDS.Supplement

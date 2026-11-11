-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_theorem_6_8
-- name    : IncApproxVC.Oblivious.theorem_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:52.403452+00:00
-- url     : https://prove2.me/theorems/c33f827b-e2dc-4f18-bd49-63fb7f715390
-- title:
--   Theorem 6.8 — IncLocalVC: deterministic incremental local vertex cut in $O((\varepsilon^{-1}\nu^{1+o(1)}+\ell^{1+o(1)})\operatorname{poly}\log n)$ total time
-- statement:
--   There is a deterministic incremental local vertex cut algorithm. Its input is an initial simple graph $G=(V,E)$ with $m$ edges, given as adjacency lists, a source $s$, integers $k\in[1,n]$ and $\nu\in[1,n^2]$, and a fraction $\varepsilon=a/b\in(0,1)$ with $a,b\in[1,\operatorname{poly}(n)]$, such that
--   $$\nu\ \le\ \frac{n-(1+\varepsilon)k}{32n}\,\varepsilon m,$$
--   and every vertex has out-degree at least $k/2$. It processes $\ell$ edge insertions chosen by a randomness-adaptive adversary in total time $O((\varepsilon^{-1}\nu^{1+o(1)}+\ell^{1+o(1)})\operatorname{poly}\log n)$. After initialization and after every insertion it outputs
--   - YES, meaning there is a separation triple $(L,S,R)$ with $s\in L$, $|S|\le(1+\varepsilon)k$ and $\mathrm{vol}^+(L)\le 8\nu/\varepsilon$; on request it outputs such sets $L$ and $S$ in $O(\varepsilon^{-1}\nu^{1+o(1)}\operatorname{poly}\log n)$ time per query; or
--   - NO, meaning there is no separation triple $(L,S,R)$ with $s\in L$, $|S|\le k$ and $\mathrm{vol}^+(L)\le\nu$.
--
--   Formally, with the same conventions as Theorem 6.1: for every exponent $d$ there are $C>0$, $g\to 0$ and a coin-free program such that for every operation sequence the runs halt within $C(\varepsilon^{-1}\nu^{1+g(\nu)}+\ell^{1+g(\ell)})(1+\log n)^C+C$ total work for initialization and insertions and $C\varepsilon^{-1}\nu^{1+g(\nu)}(1+\log n)^C+C$ per query, the outputs are correct, and a query made while the latest output is YES writes such $L$ and $S$.
--
--   Differences from the source:
--   - reading: a randomized (or deterministic) incremental algorithm / data structure; no machine is named → one admissible program of the published randomized exact real RAM PNormReg (coin-free for a deterministic algorithm), operations fed online by runOps with the layout of IncApproxVC.Oblivious.Online; reason: the paper names no machine; this is the unit-cost exact real RAM of the published PNormReg_Machine, with free input loading so that local time bounds are meaningful
--   - reading: NO, meaning there is no separating triple (L, S, R) with s ∈ S, |S| ≤ k, and vol⁺(L) ≤ ν → NO ⇒ no separation triple with s ∈ L, |S| ≤ k and vol⁺(L) ≤ ν; reason: obvious typo (s-rooted, as in Definition 3.3, Theorem 3.7 and the proof via Lemma 6.5); as printed the theorem is false (INSIGHTS I3, n = 20 instance)
--   - reading: O((ε⁻¹ν^{1+o(1)} + ℓ^{1+o(1)}) poly log n) total, O(ε⁻¹ν^{1+o(1)} poly log n) per query; numerator and denominator in [1, poly(n)] → ∀ d ∃ C g P: a, b ≤ n^d; total work of initialization and insertions ≤ C(ε⁻¹ν^{1+g(ν)} + ℓ^{1+g(ℓ)})(1+log n)^C + C; each query ≤ C ε⁻¹ν^{1+g(ν)}(1+log n)^C + C; reason: explicit universal constants for O, o(1), poly and poly log
--   - reading: a sequence of ℓ edge insertions provided by a randomness-adaptive adversary; Optionally, the algorithm can output the corresponding set L and S → every operation sequence of insertions (keeping the graph simple) and queries; a query made while the latest output is YES writes such L and S (SetsWritten, two sets); reason: a deterministic program against every sequence covers every adaptive adversary; the optional output is a clause of the statement
--   - encoding: m and the out-degree assumption refer to the input graph → m = |E(G₀)| and deg⁺_{G₀}(v) ≥ k/2; reason: the initial graph; insertions only increase both
--   - reading: an initial graph G = (V, E) represented as an adjacency list → G₀ loaded for free as adjacency arrays: block offsets, then per vertex deg⁺ and the out-neighbours, deg⁻ and the in-neighbours (the adjacency lists of G and of ←G); reason: the representation of a directed graph that Algorithm 3 needs, since it runs IncLocalVC on both G and ←G (p. 24, lines 3–7); the in-lists add no instance and loading is free so the local time bounds are meaningful
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 22, Theorem 6.8

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity
import Definitions.Def_IncApproxVC_Oblivious_Online

open Filter Topology Classical

namespace IncApproxVC.Oblivious

/-- **Theorem 6.8** (`IncLocalVC`, deterministic incremental local vertex cut), p. 22. For every
exponent `d` there are `C > 0`, a function `g → 0` and one coin-free admissible program `P` such that
the following holds for every `n`, every initial graph `G₀` on `Fin n` given as adjacency lists in
which every vertex has out-degree at least `k/2`, every source `s`, all integers `k ∈ [1, n]`,
`ν ∈ [1, n²]`, `ε = a/b ∈ (0, 1)` with `a, b ∈ [1, n^d]` and
`ν ≤ (n − (1 + ε)k)/(32n) · ε m` (`m = |E(G₀)|`), and every sequence of operations (edge
insertions keeping the graph simple, and set-output queries), fed online with the header
`[0, n, s, k, ν, a, b]`:
* every run halts, and the initialization and the `ℓ` insertions take total work at most
  `C (ε⁻¹ ν^{1+g(ν)} + ℓ^{1+g(ℓ)}) (1 + log n)^C + C`;
* after initialization and after every insertion the output (real cell `−1`) is `1` (YES) and the
  current graph has a separation triple `(L, S, R)` with `s ∈ L`, `|S| ≤ (1 + ε)k` and
  `vol⁺(L) ≤ 8ν/ε`, or it is `0` (NO) and the current graph has no separation triple `(L, S, R)`
  with `s ∈ L`, `|S| ≤ k` and `vol⁺(L) ≤ ν` (the page prints `s ∈ S` here, a typo);
* every query takes work at most `C ε⁻¹ ν^{1+g(ν)} (1 + log n)^C + C`, and a query made while the
  latest output is YES writes such sets `L` and `S` (`SetsWritten`, two sets). -/
theorem theorem_6_8 :
    ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∃ P : PNormReg.Program, PNormReg.Admissible P ∧ CoinFree P ∧
      ∀ n : ℕ, ∀ G₀ : Digraph (Fin n), ∀ s : Fin n, ∀ k ν a b : ℕ,
        1 ≤ k → k ≤ n → 1 ≤ ν → ν ≤ n ^ 2 → 1 ≤ a → a ≤ n ^ d → 1 ≤ b → b ≤ n ^ d → a < b →
        (ν : ℝ) ≤ ((n : ℝ) - (1 + (a : ℝ) / b) * k) / (32 * n) * ((a : ℝ) / b) *
          (G₀.numEdges : ℝ) →
        (∀ v : Fin n, (k : ℝ) / 2 ≤ (G₀.outDeg v : ℝ)) →
        ∀ ops : List (LocalOp n), (LocalOp.toInstance G₀ ops).Valid →
          let ε : ℝ := (a : ℝ) / b
          let ℓ : ℕ := LocalOp.numInsertions ops
          let Ttot : ℝ := C * (ε⁻¹ * (ν : ℝ) ^ (1 + g ν) + (ℓ : ℝ) ^ (1 + g ℓ)) *
            (1 + Real.log n) ^ C + C
          let Tq : ℝ := C * (ε⁻¹ * (ν : ℝ) ^ (1 + g ν)) * (1 + Real.log n) ^ C + C
          let mops := localOps [0, (n : ℤ), vword s, (k : ℤ), (ν : ℤ), (a : ℤ), (b : ℤ)] G₀ ops
          let fuel : ℕ := ⌊Ttot + Tq⌋₊
          let IsOutput : ℕ → Prop := fun j => j = 0 ∨ ∃ u v, ops[j - 1]? = some (LocalOp.insert u v)
          (∀ j, j ≤ ops.length → (runOps P noCoins fuel mops (j + 1)).halted = true) ∧
          ((∑ j ∈ (Finset.range (ops.length + 1)).filter IsOutput,
              opWork P noCoins fuel mops j : ℕ) : ℝ) ≤ Ttot ∧
          (∀ j, ops[j]? = some LocalOp.query → (opWork P noCoins fuel mops (j + 1) : ℝ) ≤ Tq) ∧
          (∀ j, j ≤ ops.length → IsOutput j →
            ((runOps P noCoins fuel mops (j + 1)).core.mem (-1) = 1 ∧
                ∃ L S R : Finset (Fin n),
                  (LocalOp.graphAfterOps G₀ ops j).IsSeparationTriple L S R ∧ s ∈ L ∧
                  (S.card : ℝ) ≤ (1 + ε) * k ∧
                  ((LocalOp.graphAfterOps G₀ ops j).vol L : ℝ) ≤ 8 * ν / ε) ∨
              ((runOps P noCoins fuel mops (j + 1)).core.mem (-1) = 0 ∧
                ¬ ∃ L S R : Finset (Fin n),
                  (LocalOp.graphAfterOps G₀ ops j).IsSeparationTriple L S R ∧ s ∈ L ∧
                  S.card ≤ k ∧ ((LocalOp.graphAfterOps G₀ ops j).vol L : ℝ) ≤ ν)) ∧
          (∀ j, ops[j]? = some LocalOp.query →
            (∃ j', j' ≤ j ∧ IsOutput j' ∧
              (∀ j'', j' < j'' → j'' ≤ j → ops[j'' - 1]? = some LocalOp.query) ∧
              (runOps P noCoins fuel mops (j' + 1)).core.mem (-1) = 1) →
            ∃ L S : Finset (Fin n), SetsWritten (runOps P noCoins fuel mops (j + 2)) 2 ![L, S] ∧
              ∃ R : Finset (Fin n),
                (LocalOp.graphAfterOps G₀ ops (j + 1)).IsSeparationTriple L S R ∧ s ∈ L ∧
                (S.card : ℝ) ≤ (1 + ε) * k ∧
                ((LocalOp.graphAfterOps G₀ ops (j + 1)).vol L : ℝ) ≤ 8 * ν / ε) := by sorry

end IncApproxVC.Oblivious

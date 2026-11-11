-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_theorem_3_12
-- name    : IncApproxVC.Oblivious.theorem_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:19.816794+00:00
-- url     : https://prove2.me/theorems/0e9131b0-2a1f-4728-a564-d7540ac50fa2
-- title:
--   Theorem 3.12 — deterministic incremental threshold $\alpha$-penalty cut in $O((F^*/\alpha+\ell)^{1+o(1)}\operatorname{poly}\log n)$ time, with a maintained set $X$
-- statement:
--   There is a deterministic incremental algorithm for threshold $\alpha$-penalty cut. Given an initial simple graph $G_0$ on $n$ vertices (as adjacency lists), a vertex $s$, $\alpha=p/q$ with integers $1\le p,q\le\operatorname{poly}(n)$ and a threshold $F^*>0$, and then $\ell$ edge insertions one at a time, it runs in total time
--   $$O\Big(\big(F^*/\alpha+\ell\big)^{1+o(1)}\operatorname{poly}\log n\Big).$$
--   After initialization and after every insertion it outputs YES or NO, YES exactly when the current graph has a set $S\ni s$ with $|\partial^+(S)|+\alpha\,\mathrm{vol}^+(S)\le F^*$. It moreover maintains a set $X$ with $|X|,\mathrm{vol}^+(X)\in O(F^*/\alpha+\ell)$ such that whenever the output is YES there is such an $S$ with $S\subseteq X$.
--
--   Formally: for every exponent $a$ there are $C>0$, $g:\mathbb R\to\mathbb R$ with $g(x)\to 0$ and a coin-free program such that, for $p,q\le n^a$, every run halts, the total work is at most $C x^{1+g(x)}(1+\log n)^C+C$ with $x=F^*/\alpha+\ell$, and after $i$ insertions $|X|$ and $\mathrm{vol}^+_{G_i}(X)$ are at most $C(F^*/\alpha+i)+C$.
--
--   **Formalization Note.** Header $[0,n,s,p,q]$ and the real word $F^*$; output in real cell $-1$ ($1$ = YES, $0$ = NO); $X$ in integer cells $0,\dots,n-1$.
--
--   Differences from the source:
--   - reading: a randomized (or deterministic) incremental algorithm / data structure; no machine is named → one admissible program of the published randomized exact real RAM PNormReg (coin-free for a deterministic algorithm), operations fed online by runOps with the layout of IncApproxVC.Oblivious.Online; reason: the paper names no machine; this is the unit-cost exact real RAM of the published PNormReg_Machine, with free input loading so that local time bounds are meaningful
--   - reading: O((F*/α + ℓ)^{1+o(1)} poly log n), α = p/q with 1 ≤ p, q ≤ poly(n) → ∀ a ∃ C g P: p, q ≤ n^a and total work ≤ C·x^{1+g(x)}·(1+log n)^C + C with x = F*/α + ℓ, g → 0; reason: explicit universal constants for O, o(1), poly and poly log
--   - reading: After every edge insertion, the algorithm outputs YES or NO → an output after initialization (i = 0) and after every insertion; reason: Definition 3.10 asks for the first insertion after which no such S exists (possibly none inserted yet), and Corollary 3.13 uses the theorem with ℓ = 0
--   - reading: maintains a set X with |X|, vol⁺(X) ∈ O(F*/α + ℓ) → X decoded from integer cells 0..n−1; after i insertions |X| and vol⁺_{G_i}(X) are ≤ C(F*/α + i) + C; reason: a fixed decoding of the maintained set; bounding at time i by i is equivalent to the bound by ℓ, since the theorem holds for every prefix of the insertion sequence and the online run on a prefix is the same
--   - encoding: threshold F* > 0 → F* : ℝ given as a real word; reason: Definition 3.9 allows any F* > 0
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 9, Theorem 3.12 (restated p. 15)

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_Cuts
import Definitions.Def_IncApproxVC_Oblivious_Online

open Filter Topology

namespace IncApproxVC.Oblivious

/-- **Theorem 3.12** (deterministic incremental threshold `α`-penalty cut), p. 9. For every exponent
`a` (the `poly(n)` bound on `p, q`) there are `C > 0`, a function `g → 0` and one coin-free admissible
program `P` such that for every `n`, every valid incremental instance on `Fin n` (initial graph `G₀`
given as adjacency lists, `ℓ` insertions), every vertex `s`, all integers `1 ≤ p, q ≤ n^a` with
`α = p/q`, and every threshold `F* > 0`, fed online with the header `[0, n, s, p, q]` and the real
word `F*`:
* every run halts and the total work is at most `C x^{1+g(x)} (1 + log n)^C + C`, `x = F*/α + ℓ`;
* after initialization and after the `i`-th insertion, the output (real cell `−1`) is `1` (YES) or
  `0` (NO), and it is YES exactly when the current graph `G_i` has a set `S ∋ s` with
  `|∂⁺(S)| + α vol⁺(S) ≤ F*`;
* the maintained set `X` (integer cells `0, …, n − 1`) has `|X| ≤ C (F*/α + i) + C` and
  `vol⁺_{G_i}(X) ≤ C (F*/α + i) + C`, and whenever the output is YES some `S ∋ s` with `S ⊆ X` has
  score at most `F*`. -/
theorem theorem_3_12 :
    ∀ a : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∃ P : PNormReg.Program, PNormReg.Admissible P ∧ CoinFree P ∧
      ∀ n : ℕ, ∀ I : IncInstance n, I.Valid → ∀ s : Fin n, ∀ p q : ℕ,
        1 ≤ p → p ≤ n ^ a → 1 ≤ q → q ≤ n ^ a → ∀ Fstar : ℝ, 0 < Fstar →
          let α : ℝ := (p : ℝ) / q
          let x : ℝ := Fstar / α + I.ins.length
          let T : ℝ := C * x ^ (1 + g x) * (1 + Real.log n) ^ C + C
          let mops := insertionOps [0, (n : ℤ), vword s, (p : ℤ), (q : ℤ)] [Fstar] I
          (∀ i, i ≤ I.ins.length → (runOps P noCoins ⌊T⌋₊ mops (i + 1)).halted = true) ∧
          ((runOps P noCoins ⌊T⌋₊ mops (I.ins.length + 1)).work : ℝ) ≤ T ∧
          ∀ i, i ≤ I.ins.length →
            ((runOps P noCoins ⌊T⌋₊ mops (i + 1)).core.mem (-1) = 1 ∨
                (runOps P noCoins ⌊T⌋₊ mops (i + 1)).core.mem (-1) = 0) ∧
            ((runOps P noCoins ⌊T⌋₊ mops (i + 1)).core.mem (-1) = 1 ↔
                ∃ S : Finset (Fin n), s ∈ S ∧ (I.graphAfter i).penaltyScore α S ≤ Fstar) ∧
            ((runOps P noCoins ⌊T⌋₊ mops (i + 1)).core.mem (-1) = 1 →
                ∃ S : Finset (Fin n), s ∈ S ∧
                  S ⊆ maintainedSet (runOps P noCoins ⌊T⌋₊ mops (i + 1)) ∧
                  (I.graphAfter i).penaltyScore α S ≤ Fstar) ∧
            (((maintainedSet (n := n) (runOps P noCoins ⌊T⌋₊ mops (i + 1))).card : ℝ) ≤
                C * (Fstar / α + i) + C) ∧
            (((I.graphAfter i).vol (maintainedSet (runOps P noCoins ⌊T⌋₊ mops (i + 1))) : ℝ) ≤
                C * (Fstar / α + i) + C) := by sorry

end IncApproxVC.Oblivious

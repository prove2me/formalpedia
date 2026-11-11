-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_lemma_24
-- name    : MinorFreeSTC.Main.lemma_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:19:47.164214+00:00
-- url     : https://prove2.me/theorems/bf4c4cdf-75de-4166-a421-c4731b4f4363
-- title:
--   Lemma 24 — separated neighborhood covers give (1+ϵ)-distortion spanning tree covers of size τ·(O(1/ϵ))^{r+1}·log(1/s + αr log n/ϵ) w.h.p.
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $G$ be a connected $n$-vertex $K_r$-minor-free weighted graph (weights in $[1,n^k]$) and fix $\alpha,\tau\ge1$, $s>0$. **(E)** If for every $\Delta>0$ there is a $\tau$-size, $\alpha$-padded, $\Delta$-diameter, $s$-separated neighborhood cover of $G$, then for every $\epsilon\in(0,1)$ there is a $(1+\epsilon)$-distortion spanning tree cover $\mathcal T$ of $G$ with
--   $$|\mathcal T|\ \le\ \tau\cdot\Big(\frac c\epsilon\Big)^{r+1}\cdot\log_2\!\Big(\frac1s+\frac{\alpha r\log_2n}{\epsilon}\Big).$$
--   **(A)** For every $c'>1$ one admissible oracle program, for all $r,k,\alpha,\tau,s,\epsilon$ with constants $C,K$, given $(G,\epsilon,r,\alpha,\tau,s)$ and an oracle answering every query $\Delta>0$ with such a cover, outputs such a $\mathcal T$ within $Cn^K+C$ steps, failing with coin-tape measure at most $n^{-c'}$.
--
--   Combined with Theorem 4 this gives Theorem 11.
--
--   **Formalization Note.** As printed the bound is negative at $n=1$, $s>1$, and the statement is false there (insight I2); it is stated as printed.
--
--   Differences from the source:
--   - reading: 'Suppose that, for every ∆ > 0, we can construct a … cover. Then … we can, with high probability, construct … If the separated neighborhood covers can be constructed in polynomial time, then so can …' → (E) if for every ∆ > 0 such a cover exists, the conclusion's object exists; (A) a black-box reduction: one admissible oracle program which, with an oracle returning some valid such cover for every query ∆ > 0 (an arbitrary such oracle), runs within the stated step bound counting one step per oracle call and fails with coin-tape measure ≤ n^{−c}; reason: the conditional statement has an existence and an algorithmic reading; the black-box reading is what the proof does and is stronger than 'poly-time oracle implies poly-time'; one step per call is equivalent to one step per output cell since an answer has at most ⌊τ⌋·n + 1 cells and C may depend on τ
--   - reading: (O(1/ϵ))^{r+1} → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 51, Lemma 24

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_RamseyLST_Main_RamseySpanningTree
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Machine

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Lemma 24** (p. 51). There is a universal `c` such that for every connected `K_r`-minor-free
weighted graph and `α, τ ≥ 1`, `s > 0`: **(E)** if for every `∆ > 0` there is a `τ`-size,
`α`-padded, `∆`-diameter, `s`-separated neighborhood cover, then for every `ϵ ∈ (0, 1)` there is a
`(1 + ϵ)`-distortion spanning tree cover of size at most `τ (c/ϵ)^{r+1} log(1/s + αr log n/ϵ)`;
**(A)** for every `c' > 1` one oracle program, given such covers by an oracle answering every
`∆ > 0`, computes such a cover in `C n^K + C` steps (one step per oracle call) with failure
probability at most `n^{−c'}`. -/
theorem lemma_24 :
    ∃ c : ℝ, 0 < c ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ)
        (α τ s : ℝ),
        Connected G → MinorFree G r → AspectBounded G k → 1 ≤ α → 1 ≤ τ → 0 < s →
        (∀ Δ : ℝ, 0 < Δ → ∃ (m : ℕ) (𝒞 : Fin m → Finset (Finset V)), IsSepCover G m 𝒞 τ α Δ s) →
        ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
          ∃ (m : ℕ) (T : Fin m → RamseyLST.Main.SpanningTree G),
            IsSpanningTreeCover G m T (1 + ϵ) ∧
              (m : ℝ) ≤ τ * (c / ϵ) ^ (r + 1) * Real.logb 2 (1 / s + α * r * Real.logb 2 (Fintype.card V) / ϵ)) ∧
      ∀ c' : ℝ, 1 < c' → ∃ A : Program, Admissible A ∧
        ∀ (r k : ℕ) (α τ s ϵ : ℝ), 1 ≤ α → 1 ≤ τ → 0 < s → 0 < ϵ → ϵ < 1 → ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V)
            (E : Encoding G) (O : Oracle),
            Connected G → MinorFree G r → AspectBounded G k →
            (∀ Δ : ℝ, 0 < Δ → CoverOut E (fun m 𝒞 => IsSepCover G m 𝒞 τ α Δ s) (O Δ)) →
            ComputesWHP A O (E.cells ++ [ϵ, (r : ℝ), α, τ, s])
              (TreesOut E fun m T =>
                IsSpanningTreeCover G m T (1 + ϵ) ∧
              (m : ℝ) ≤ τ * (c / ϵ) ^ (r + 1) * Real.logb 2 (1 / s + α * r * Real.logb 2 (Fintype.card V) / ϵ))
              (C * (Fintype.card V : ℝ) ^ K + C) ((Fintype.card V : ℝ) ^ (-c')) := by sorry

end MinorFreeSTC.Main

-- Prove2me | Theorems.Thm_IncrementalER_theorem_1_1
-- name    : IncrementalER.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:30.716583+00:00
-- url     : https://prove2.me/theorems/ad5b0873-3ac0-45c1-a769-1d2877622ba6
-- title:
--   Theorem 1.1, p.4 — incremental $(1\pm\varepsilon)$-approximate energies of sparse demands in total time $M(1/\varepsilon)^{O(\sqrt{\log n\log\log n})}$, correct w.h.p.
-- statement:
--   Let $G=(V,E,c)$ be an initially empty graph on $n\ge1$ vertices and $0<\varepsilon<1/2$. A data structure receives, one at a time, a sequence of $M$ operations fixed in advance (an oblivious adversary):
--
--   1. $\mathrm{InsertEdge}(u,v,c)$ inserts an edge $(u,v)$ with capacity $c>0$; the ratio of any two inserted capacities is at most $n^b$;
--   2. $\mathrm{Query}(d)$ gives a demand $d\in\mathbb R^V$ with at most $(1+\log n)^a$ nonzero entries, $d^\top\mathbf 1=0$, and $d^\top\mathbf 1_C=0$ for every connected component $C$ of the current graph, and must return an estimate $\hat{\mathcal E}(d)$ with
--   $$(1-\varepsilon)\,d^\top L_G^\dagger d\le\hat{\mathcal E}(d)\le(1+\varepsilon)\,d^\top L_G^\dagger d,$$
--   where $G$ is the graph of the edges inserted before the query.
--
--   **Theorem.** For all exponents $a,b\in\mathbb N$ and all constants $c>1$ and $\kappa>0$ there are a constant $C>0$ and one program $P$ of the randomized real RAM such that for every $n\ge1$, every $\varepsilon\in(0,1/2)$ and every such sequence of $M$ operations:
--
--   1. on every outcome of the coins, every operation's run halts and the total work is at most
--   $$C\,M\,(1/\varepsilon)^{C\sqrt{\log n\cdot\log\log n}};$$
--   2. if $M\le n^\kappa$, the probability that some query's answer lies outside its interval is at most $n^{-c}$.
--
--   For $d=\mathbf 1_s-\mathbf 1_t$ this maintains $(1\pm\varepsilon)$-approximate effective resistances between arbitrary pairs under edge insertions in $n^{o(1)}$ amortized time per operation whenever $\varepsilon\ge1/\log^{O(1)}n$.
--
--   **Formalization Note** The program runs on the published real RAM `PNormReg.Machine` (exact $+,-,\times,\div$, $\sqrt{\cdot}$, $|r|^s$, rational literals, integer pointers, fair coins; no floor). Operations are written into its memory one at a time (`runOps`); the work counter accumulates over all of them. The failure probability is an upper bound on the outer measure of the set of coin tapes on which some query fails (a run that does not halt within the time bound counts as a failure).
--
--   Differences from the source:
--   - reading: "There is a data structure … the algorithm takes total time" (no machine named) → one finite admissible program of the randomized exact real RAM PNormReg.Machine, fed the operations online by runOps (memory, coin cursor and work kept between operations); reason: the paper names no machine; unit-cost exact reals without floor cannot pack words, so the existential is not trivialized, and √ and powers are the primitives the algorithm uses (exp in the MWU loops)
--   - reading: "For a sequence of O(m) interleaved edge insertions and query calls, … total time O(m · (1/ε)^{O(√log n log log n)})" → for M operations, total work ≤ C·M·(1/ε)^{C√(log n · log log n)}, one constant C for both O's, chosen before n, ε and the sequence; reason: M ≥ the number m of insertions and the bound is linear, so the two forms agree up to the constant
--   - reading: Õ(1) nonzero entries; polynomially bounded capacity ratio → ≤ (1 + log n)^a nonzero entries and capacity ratio ≤ n^b, for every a, b ∈ ℕ quantified before C and P; reason: Õ hides factors polynomial in log N (p.10); the exponents are the theorem's fixed parameters
--   - reading: "For m polynomially bounded, the data structure is correct with high probability", w.h.p. = probability ≥ 1 − N^{−c} for any fixed constant c > 1 (p.10) → for every c > 1 and κ > 0 (before C and P): if M ≤ n^κ, failure probability ≤ n^{−c}; reason: the paper's definition of high probability, with N = n
--   - reading: time bound and "m polynomially bounded" in the same theorem → the time clause holds for every valid sequence and every coin tape, without M ≤ n^κ; reason: the printed theorem attaches "m polynomially bounded" to correctness only, and the proof caps total work by budgets on every run (p.42)
--   - generalization: InsertEdge(u, v, c) inserts an edge (u, v) → u = v is allowed; a loop contributes 0 to L_G; reason: every sequence of the paper is a sequence of the Lean statement
--   - encoding: log and √ in (1/ε)^{O(√log n log log n)} → natural logarithms, Real.sqrt (0 on negatives, so the bound is C·M for n ≤ 15); reason: any other base or a clamp gives a larger bound, so this is the strongest form
--   - encoding: Query(d) given d ∈ ℝ^V with Õ(1) nonzero entries → d given as the list of its nonzero entries (distinct vertices, nonzero values); reason: the list is the sparse representation the statement presupposes
--   - encoding: "correct with high probability" → an upper bound n^{−c} on the outer measure of the set of coin tapes on which some query's answer is outside its interval or its run has not halted; reason: an upper bound on outer measure needs no measurability and is the stronger form
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 1.1 and footnote 1, p.4; "with high probability" and Õ, p.10

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncrementalER_energy
import Definitions.Def_IncrementalER_runOps

namespace IncrementalER

/-- **Theorem 1.1** (incremental `(1 ± ε)`-approximate energies of sparse demands).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 1.1 and
footnote 1, p.4; "with high probability" and `Õ` as defined on p.10.

For every support exponent `a`, capacity-ratio exponent `b`, failure exponent `c > 1` and length
exponent `κ > 0` there are a constant `C > 0` and one admissible program `P` of the real RAM such
that for every `n ≥ 1`, every `ε ∈ (0, 1/2)` and every valid sequence `ops` of `M` operations:
on every coin tape every operation's run halts and the total work is at most
`C · M · (1/ε)^{C √(log n · log log n)}`; and if `M ≤ n^κ`, the probability that some query's
answer lies outside `[(1 − ε) d⊤L†_G d, (1 + ε) d⊤L†_G d]` (with `G` the graph of the edges inserted
before the query) is at most `n^{−c}`.

**Formalization Note.**
* The machine is the published randomized exact real RAM `PNormReg.Machine`, a reading: the paper
  names none. Operations are fed online by `runOps` (cell layout, reset of registers, memory,
  cursor and work kept: see `Def_IncrementalER_runOps`). The sequence is fixed before the coin
  tape (oblivious adversary).
* Quantifier order: `a b c κ` first, then `∃ C ∃ P`, then `n ε ops`. `a` makes the `Õ(1)`
  support `≤ (1 + log n)^a`, `b` the capacity ratio `≤ n^b`, `c` the "any fixed constant `c > 1`"
  of p.10, `κ` "`m` polynomially bounded". One `C` serves both `O`'s of the time bound.
* `M` is the number of operations; the printed "`O(m)` operations … `O(m ·…)`" is the same claim
  since `M ≥` the number of insertions and the bound is linear in it.
* Natural logarithms; `Real.sqrt` of a negative product (`n ≤ 15`) is `0`, and then the bound is
  `C · M`.
* The time clause holds on every tape and for every valid sequence, without `M ≤ n^κ`: the printed
  theorem attaches "`m` polynomially bounded" to correctness only.
* The failure set is bounded above in outer measure; a query whose run did not halt within the
  fuel counts as a failure. -/
theorem theorem_1_1 :
    ∀ a b : ℕ, ∀ c κ : ℝ, 1 < c → 0 < κ →
      ∃ C : ℝ, 0 < C ∧ ∃ P : PNormReg.Program, PNormReg.Admissible P ∧
        ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∀ ops : List (Op n), ValidSeq a b ops →
            (∀ ω : ℕ → Bool,
                (∀ j < ops.length,
                  (runOps P ε ops ⌊timeBound C n ε ops.length⌋₊ ω (j + 1)).halted = true) ∧
                ((runOps P ε ops ⌊timeBound C n ε ops.length⌋₊ ω ops.length).work : ℝ) ≤
                  timeBound C n ε ops.length) ∧
            ((ops.length : ℝ) ≤ (n : ℝ) ^ κ →
              PNormReg.coinTape {ω | ∃ j : ℕ, ∃ h : j < ops.length, ∃ l : List (Fin n × ℝ),
                  ops[j] = .query l ∧
                  ¬ ((runOps P ε ops ⌊timeBound C n ε ops.length⌋₊ ω (j + 1)).halted = true ∧
                    answer P ε ops ⌊timeBound C n ε ops.length⌋₊ ω j ∈
                      Set.Icc ((1 - ε) * energy (edgeLap (edgesBefore ops j)) (sparseVec l))
                        ((1 + ε) * energy (edgeLap (edgesBefore ops j)) (sparseVec l)))}
                ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))) := by sorry

end IncrementalER

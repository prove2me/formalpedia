-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_9_1
-- name    : MetricTSPSublinear.lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:21.557057+00:00
-- url     : https://prove2.me/theorems/c82c29c3-c318-4dda-a98d-de5d2e03184f
-- title:
--   Lemma 9.1 — the estimator $\widehat L$: $\tilde O(n^{2-a/10})$ queries, $0\le\widehat L\le K$, and $\widehat L\ge\frac{1+\varepsilon}2\widehat M$ when $D\le\varepsilon M$
-- statement:
--   For sufficiently small $a,\varepsilon>0$ there is a randomized algorithm that, given query access to an $n$-point metric $d$ and an estimate $\widehat M$ with $M\le\widehat M\le(1+O(\varepsilon))M$, uses $\tilde O(n^{2-a/10})$ distance queries and with probability at least $2/3$ returns $\widehat L$ with
--
--   1. $0\le\widehat L\le K$, and
--   2. if $D=M-K\le\varepsilon M$, then $\widehat L\ge\frac{1+\varepsilon}{2}\widehat M$.
--
--   Precisely: for every constant $c>0$ there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$ there is $a_0>0$ such that for every $a\in(0,a_0]$ there are a program $P$ of the distance-oracle real RAM with fair coins, constants $C$, $k$ and a step bound $B(n)$ such that, for every $n$, metric $d$ and $\widehat M$ with $M\le\widehat M\le(1+c\varepsilon)M$, every run of $P$ on $(n,\widehat M)$ halts within $B(n)$ steps after at most $C(n+2)^{2-a/10}\log(n+2)^k$ queries, and on at least $2/3$ of the coin tapes the output satisfies 1 and 2.
--
--   This is the estimator of Section 9; the decision rule of Theorem 1 compares $\widehat L$ with $(1+\varepsilon)\widehat M/2$.
--
--   Differences from the source:
--   - reading: for sufficiently small a, ε > 0 → ∀ c > 0, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀], ∃ a₀ > 0, ∀ a ∈ (0, a₀], ∃ program and constants; reason: the program and constants depend on a and ε only, never on the instance; a is the exponent after the refinement loop
--   - reading: an estimate M̂ with M ≤ M̂ ≤ (1 + O(ε))M (p.9) → for every constant c > 0 (chosen first, ε₀ depending on it), every M̂ with M ≤ M̂ ≤ (1 + cε)M is accepted; reason: the strongest reading of the unspecified O(ε) constant; the proof (p.42) ends with L − τ ≥ 3M/4 and L̂ ≥ L − τ − 4εM̂, which gives L̂ ≥ (1 + ε)M̂/2 for ε small enough given c
--   - reading: the algorithm uses Õ(n^{2−a/10}) distance queries → an admissible SublinearSteiner program halting within B(n) steps on every tape with at most C (n+2)^{2−a/10} log(n+2)^k queries on every tape; reason: worst-case bounds (p.42: a subroutine over budget stops and returns zero); the lemma claims no time bound, so B is any function of n
--   - encoding: the algorithm's input (V, d) and M̂ → n in integer memory (terminal set Finset.univ), M̂ in real memory cell 0, d only through query; reason: the same information
--   - encoding: with probability 2/3 → at least 2/3 of the 2^{B(n)} coin tapes, both clauses on one event; reason: a run of B(n) steps reads at most B(n) fair coins
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
--   - encoding: M = w(T), the MST weight → DoublingMST.mstWeight d, the infimum of the edge-weight sum over spanning trees of the complete graph on Fin n, with edge weight min(d u v, d v u); reason: equals the MST weight for a metric
--   - encoding: K, the optimal value of the Cut LP (P) → cutLP d Finset.univ, the infimum of the objective of (P) over its feasible points; reason: the LP's optimum for a metric
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §9, Lemma 9.1, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_SublinearSteiner_Machine
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_runWithEstimate
import Definitions.Def_DoublingMST_mstWeight

open scoped Classical

namespace MetricTSPSublinear

/-- **Lemma 9.1.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §9, p.33 (PDF p.35): "For sufficiently small a, ε > 0, the algorithm uses Õ(n^{2−a/10})
distance queries, and returns an estimate L̂ satisfying the following with probability 2/3: 1. 0 ≤ L̂ ≤ K, and
2. if D ≤ εM, then L̂ ≥ ((1+ε)/2) M̂." The algorithm is given `M̂` with `M ≤ M̂ ≤ (1 + O(ε))M` (p.9).

For every constant `c > 0` (the constant of the page's `O(ε)`) there is `ε₀ > 0` such that for every
`ε ∈ (0, ε₀]` there is `a₀ > 0` such that for every `a ∈ (0, a₀]` there are an
admissible program `P` of the distance-oracle real RAM with fair coins (`SublinearSteiner`), constants `C`, `k` and
a step bound `B(n)` with the following property. For every `n`, every metric `d` on `Fin n` and every real `M̂`
with `M ≤ M̂ ≤ (1 + cε)M` (`M = DoublingMST.mstWeight d`), started with `n` and `M̂` (`runWithEstimate`):
1. on every tape of `B(n)` coins, `P` halts within `B(n)` steps after at most `C (n+2)^{2−a/10} log(n+2)^k`
   distance queries;
2. on at least `2/3` of the tapes the output `L̂` satisfies `0 ≤ L̂ ≤ K`, and `L̂ ≥ ((1+ε)/2)M̂` if
   `D = M − K ≤ εM` (`K = cutLP d Finset.univ`).

**Formalization Note.**
* "For sufficiently small a, ε" is read as `∃ ε₀ ∀ ε ≤ ε₀ ∃ a₀ ∀ a ≤ a₀`, after the constant `c`: the program and the constants may depend
  on `a` and `ε`, not on the instance. `a` is the exponent of the bound, the value after the refinement loop of §5.2.
* `M̂ ≤ (1 + O(ε))M` is read as `M̂ ≤ (1 + cε)M` for every constant `c > 0`, with `ε₀` depending on `c`
  (the strongest reading: the proof, p.42 (PDF p.44), ends with `L − τ ≥ 3M/4` and `L̂ ≥ L − τ − 4εM̂`, which gives
  `L̂ ≥ (1 + ε)M̂/2` for `ε` small enough given `c`); the algorithm must succeed for every such `M̂`.
* `Õ(·)` is `C (n+2)^{2−a/10} log(n+2)^k` (the `+2` keeps the logarithm positive at `n ≤ 1`), a worst-case bound
  on every tape (p.42: a subroutine that exceeds its query budget stops and returns zero). The lemma claims no time
  bound, so `B` is any function of `n`.
* `M̂` is in real memory cell `0`; the integer memory holds `n` (terminal set `Finset.univ`). Probability is the
  fraction of the `2^{B(n)}` tapes. Both clauses of the estimate hold on one event. -/
theorem lemma_9_1 :
    ∀ c : ℝ, 0 < c → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∃ (P : SublinearSteiner.Program) (C : ℝ) (k : ℕ) (B : ℕ → ℕ), SublinearSteiner.Admissible P ∧
        ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d → ∀ Mhat : ℝ,
          DoublingMST.mstWeight d ≤ Mhat → Mhat ≤ (1 + c * ε) * DoublingMST.mstWeight d →
          (∀ tape : Fin (B n) → Bool,
              (runWithEstimate P d Mhat tape (B n)).output.isSome ∧
              ((runWithEstimate P d Mhat tape (B n)).queries : ℝ) ≤
                C * ((n : ℝ) + 2) ^ (2 - a / 10) * Real.log ((n : ℝ) + 2) ^ k) ∧
          (2 / 3 : ℝ) * 2 ^ (B n) ≤
            ((Finset.univ.filter (fun tape : Fin (B n) → Bool => ∃ L : ℝ,
                (runWithEstimate P d Mhat tape (B n)).output = some L ∧
                0 ≤ L ∧ L ≤ cutLP d Finset.univ ∧
                (DoublingMST.mstWeight d - cutLP d Finset.univ ≤ ε * DoublingMST.mstWeight d →
                  (1 + ε) / 2 * Mhat ≤ L))).card : ℝ) := by sorry

end MetricTSPSublinear

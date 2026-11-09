-- Prove2me | Theorems.Thm_MetricTSPSublinear_theorem_1
-- name    : MetricTSPSublinear.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:24:25.05597+00:00
-- url     : https://prove2.me/theorems/580bc9ab-c42a-40e6-b8d9-2ead9dbd8130
-- title:
--   Theorem 1 — a $(2-\delta)$-approximation of metric TSP with $O(n^{2-\varepsilon})$ queries and $O(n^{2-\gamma})$ time
-- statement:
--   There are absolute constants $\varepsilon,\delta,\gamma>0$ and a randomized algorithm that, given query access to the distance matrix of any $n$-point metric $d$, makes $O(n^{2-\varepsilon})$ distance queries, runs in time $O(n^{2-\gamma})$, and with probability at least $2/3$ returns an estimate $\widehat{\mathrm{TSP}}$ with
--   $$\mathrm{TSP}\ \le\ \widehat{\mathrm{TSP}}\ \le\ (2-\delta)\,\mathrm{TSP},$$
--   where $\mathrm{TSP}$ is the length of a shortest Hamiltonian cycle. The constants do not depend on $n$ or the metric; the algorithm uses only distance queries, with no MST supplied.
--
--   Precisely: there are $\varepsilon,\delta,\gamma>0$, a program $P$ of the distance-oracle real RAM with fair coins and a constant $C$ such that for every $n$ and every metric $d$ on $n$ points, with $B=\lceil C(n+1)^{2-\gamma}\rceil$, every run of $P$ halts within $B$ steps after at most $C(n+1)^{2-\varepsilon}$ queries, and on at least $2/3$ of the $2^B$ coin tapes its output lies in $[\mathrm{TSP},(2-\delta)\mathrm{TSP}]$.
--
--   This answers Open Problem 71 of sublinear.info: before it, the best sublinear-query estimate of metric TSP was the factor $2$ given by the MST weight.
--
--   Differences from the source:
--   - reading: a randomized algorithm; running time → an admissible program of the published SublinearSteiner real RAM (unit-cost real arithmetic and comparisons, integer pointer ±, rational literals, fair coins, no floor, sqrt, exp or log); time = executed instructions; reason: the page names no machine; this is the strong reading, every extra instruction would weaken the theorem
--   - reading: O(n^{2−ε}) queries, O(n^{2−γ}) time → one constant C chosen before n and d; at most C (n+1)^{2−ε} queries and halting within ⌈C (n+1)^{2−γ}⌉ steps on every tape; reason: worst-case bounds (p.34: over-budget subroutines stop and return zero); n + 1 avoids a case at n = 0
--   - encoding: query access to the distance matrix, no MST supplied → input layout of SublinearSteiner with terminal set Finset.univ: integer memory I 0 = n, I (1+v) = 1; d only through query; reason: the program learns n and nothing else about d except by queries
--   - encoding: with probability at least 2/3 → at least 2/3 of the 2^B tapes Fin B → Bool, B the step bound; reason: a run of B steps reads at most B fair coins
--   - encoding: TSP, the length of a shortest Hamiltonian cycle → MetricTSP.tspOpt d; 0 for n ≤ 1 and 2d(0,1) for n = 2; reason: for n ≥ 3 the same value; for n ≤ 2 the conventional tour values
--   - encoding: an n-point metric (V, d) → DoublingMST.IsMetric d on Fin n: d u v = 0 iff u = v, symmetry, triangle inequality; reason: same instances; nonnegativity follows
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §1, Theorem 1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_SublinearSteiner_Machine
import Definitions.Def_DoublingMST_IsMetric

open scoped Classical

namespace MetricTSPSublinear

/-- **Theorem 1 (Main result).** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §1, p.1 (PDF p.3): "There exist absolute constants ε, δ > 0 and a randomized
algorithm that, given query access to the distance matrix of any n-point metric, makes O(n^{2−ε}) distance queries
and, with probability at least 2/3, returns an estimate T̂SP satisfying TSP ≤ T̂SP ≤ (2 − δ)TSP. Additionally, the
algorithm runs in O(n^{2−γ}) time for an absolute constant γ > 0." p.1 continues: "The constants ε and δ are
independent of n and of the input metric. The algorithm uses only distance queries, with no MST supplied and no
restriction to a special class of metrics."

There are `ε, δ, γ > 0`, an admissible program `P` of the distance-oracle real RAM with fair coins
(`SublinearSteiner`) and a constant `C` such that for every `n` and every metric `d` on `Fin n`, with
`B = ⌈C (n+1)^{2−γ}⌉`:
1. on every tape of `B` coins, `P` halts within `B` steps (so its time is at most `B`) after at most
   `C (n+1)^{2−ε}` distance queries;
2. on at least `2/3` of the tapes the output `T̂SP` satisfies `TSP ≤ T̂SP ≤ (2 − δ)TSP`, where
   `TSP = MetricTSP.tspOpt d`.

**Formalization Note.**
* The machine is the published `SublinearSteiner` real RAM: unit-cost real arithmetic and comparisons, integer
  pointers with `+` and `−` only, a one-way pointer-to-real cast, rational literals, fair coins as the only
  randomness, and the `query` instruction as the only access to `d`, each call counted. It has no floor, square
  root, exponential or logarithm; each of these would make the machine stronger and the theorem weaker. The page
  names no machine for "time".
* The input is the published layout with terminal set `Finset.univ`: integer memory `I 0 = n` and `I (1+v) = 1`,
  so the program learns `n` and reads `d` only through queries. No MST, MST estimate or other side information is
  given.
* `O(·)` is one constant `C` chosen before the instance, with `n + 1` for `n` so that `n = 0` needs no case.
  Both bounds are worst case, on every tape (p.34: a subroutine that exceeds its budget stops and returns zero).
* Probability is the fraction of the `2^B` tapes; a run of `B` steps reads at most `B` coins.
* For `n ≤ 2` the tour degenerates: `TSP` is `0` for `n ≤ 1` and `2 d(0,1)` for `n = 2`. -/
theorem theorem_1 :
    ∃ (ε δ γ : ℝ) (P : SublinearSteiner.Program) (C : ℝ), 0 < ε ∧ 0 < δ ∧ 0 < γ ∧
      SublinearSteiner.Admissible P ∧
      ∀ (n : ℕ) (d : Fin n → Fin n → ℝ), DoublingMST.IsMetric d →
        (∀ tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool,
            (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output.isSome ∧
            ((SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).queries : ℝ) ≤
              C * ((n : ℝ) + 1) ^ (2 - ε)) ∧
        (2 / 3 : ℝ) * 2 ^ ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ ≤
          ((Finset.univ.filter (fun tape : Fin ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊ → Bool => ∃ z : ℝ,
              (SublinearSteiner.run P Finset.univ d tape ⌈C * ((n : ℝ) + 1) ^ (2 - γ)⌉₊).output = some z ∧
              MetricTSP.tspOpt d ≤ z ∧ z ≤ (2 - δ) * MetricTSP.tspOpt d)).card : ℝ) := by sorry

end MetricTSPSublinear

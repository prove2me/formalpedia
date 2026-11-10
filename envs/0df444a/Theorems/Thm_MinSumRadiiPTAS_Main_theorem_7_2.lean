-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_theorem_7_2
-- name    : MinSumRadiiPTAS.Main.theorem_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:02:31.059207+00:00
-- url     : https://prove2.me/theorems/b1cf4874-b09b-4f07-888b-e92af68771d0
-- title:
--   Theorem 7.2 — finding a bipoint solution: at most $n^{2c_{\max}/\varepsilon^4}$ pairs, w.h.p. one with cost $\le (1+C\varepsilon)\,\mathrm{opt}$ and radii $\le \varepsilon^4\mathrm{opt}$
-- statement:
--   **Theorem 7.2** (finding a bipoint solution, p. 28; proof pp. 38–40). There are one admissible program $P$ of the randomized distance-oracle real RAM and one absolute constant $C$ such that, for every $\varepsilon \in (0, 1/10)$ and every normalised instance $(n, k, d)$ (input in the published layout), with $N = \max(n, 2)$ and $T = N^{2^{C/\varepsilon}}$: on every random tape the run has halted after $\lfloor T\rfloor$ steps with work $\le T$, having output a collection of at most $n^{2c_{\max}/\varepsilon^4}$ pairs $(S_0, S_{bp})$, $S_{bp} = (S_1, S_2, \theta)$, where for every pair $|S_0| = k_0 \le k$, $\theta \in [0, 1]$, both $S_1$ and $S_2$ cover $X = P \setminus \bigcup_{B \in S_0} B$, and $|S_{bp}| = \theta|S_1| + (1-\theta)|S_2| \le k - k_0$; and with probability at least $1 - 1/N$ (a measurable event) some pair satisfies
--   $$\mathrm{cost}(S_0) + \theta\,\mathrm{cost}(S_1) + (1-\theta)\,\mathrm{cost}(S_2) \le (1 + C\varepsilon)\,\mathrm{opt}$$
--   and every ball of $S_1 \cup S_2$ has radius at most $\varepsilon^4\,\mathrm{opt}$.
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - encoding: a set S of balls output by an algorithm, |S|, cost(S) → a ball list read from the machine; |S| is its length and cost(S) the sum over its entries, a repeated ball counted every time; reason: an output without repetitions is a set; counting repetitions only makes the size and cost bounds harder to meet
--   - generalization: a (randomized, polynomial-time) algorithm on an unspecified machine → one MinSumFPT.Admissible program of the published randomized distance-oracle real RAM (unit cost per instruction; no floor, √, log/exp or pointer multiplication; rational literals); inputs in the published initState layout (n, k, ε, δ = 0); reason: the machine has fewer primitives than any standard real RAM, so the statement implies the same statement on a richer machine
--   - generalization: "Fix ε ∈ (0, 1/10). There is an algorithm …" (an algorithm per ε) → one program P and constants chosen before ε, with ε as input in mem 0; reason: a single program for all ε specializes to an algorithm for each fixed ε; the proof's algorithm takes ε as a parameter
--   - generalization: time n^{O_ε(1)} → at most ⌊T⌋₊ steps and work ≤ T with T = N^(2^(C/ε)), N = max(n, 2), C absolute; reason: N^(2^(C/ε)) is n^{O_ε(1)} for every fixed ε; N = max(n, 2) handles the finite small-input case. Appendix C supplies this explicit dependence on ε (INSIGHTS I2)
--   - reading: running time of a randomized algorithm → worst case: on every tape ω the run has halted within the time bound with a well-formed output; reason: the paper's running times are deterministic bounds (pp. 23, 38–39); success, not time, is probabilistic
--   - reading: "produces a collection … where S_0 is a set of k_0 ≤ k balls and S_bp … a bipoint solution … of size ≤ k − k_0. With high probability, at least one pair …" → the size bound and every structural clause hold for every pair on every tape; only the existence of a good pair is the probabilistic event; reason: the sentence structure puts "with high probability" on the last clause only
--   - reading: "with high probability" → tapeLaw-probability at least 1 − 1/N, N = max(n, 2), of a measurable event; reason: the textbook 1 − n^{−c} with c = 1; the paper's components fail with probability O(1/n²) and repetition reaches any c
--   - reading: (1 + O(ε)) opt → (1 + C ε) · msrOpt d k with the same absolute C fixed before ε and the instance; reason: an O(ε) term in a statement for every ε ∈ (0, 1/10) has an absolute constant
--   - reading: the theorem's own sentence → StandingInstance d k ε (Lemma 2.1's normalisation, 1 ≤ k ≤ n); reason: p. 7 assumes the normalisation for the rest of the paper and the proof uses it (cost(OPT′) ≥ 1, opt ≤ 8k/ε, p. 39)
--   - encoding: "a collection of at most n^{2c_max/ε⁴} pairs" → a list of pairs of length at most (n : ℝ)^(2 c_max/ε⁴) (real power, raw n ≥ 1); reason: a repeated pair is counted every time, which only makes the bound harder to meet
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §7, Theorem 7.2, p. 28 (proof Appendix C.1, pp. 38–40)

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_Partition
import Definitions.Def_MinSumRadiiPTAS_Main_Machine

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Theorem 7.2** (finding a bipoint solution, p. 28; proof pp. 38–40): one admissible program `P`
and one absolute constant `C` such that, on every normalised instance with `ε ∈ (0, 1/10)` (input:
the instance in the published layout), with `N = max(n, 2)` and `T = N^(2^(C/ε))`: on every tape the
run has halted after `⌊T⌋₊` steps with work `≤ T` and a collection of at most `n^(2c_max/ε⁴)` pairs
`(S₀, (S₁, S₂, θ))`, each with `|S₀| ≤ k`, `θ ∈ [0, 1]`, `S₁` and `S₂` covering
`X = P \ ⋃_{B ∈ S₀} B` and `θ|S₁| + (1 − θ)|S₂| ≤ k − |S₀|`; and with probability at least `1 − 1/N`
some pair has `cost(S₀) + θ cost(S₁) + (1 − θ) cost(S₂) ≤ (1 + Cε) opt` and every ball of `S₁ ∪ S₂`
of radius `≤ ε⁴ opt`. -/
theorem theorem_7_2 :
    ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧ ∃ C : ℕ,
      ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ), StandingInstance d k ε →
        let N : ℕ := max n 2
        let T : ℝ := (N : ℝ) ^ ((2 : ℝ) ^ ((C : ℝ) / ε))
        let E : Set (ℕ → ℝ) := {ω | ∃ ps : List (BipointPair n),
          OutputsPairs (MinSumFPT.run P n k ε 0 d ω ⌊T⌋₊) ps ∧
            ∃ q ∈ ps,
              lcost q.S0 + (q.θ * lcost q.S1 + (1 - q.θ) * lcost q.S2) ≤
                  (1 + (C : ℝ) * ε) * msrOpt d k ∧
                ∀ B ∈ q.S1 ++ q.S2, B.radius ≤ ε ^ 4 * msrOpt d k}
        (∀ ω : ℕ → ℝ, ∃ ps : List (BipointPair n),
            OutputsPairs (MinSumFPT.run P n k ε 0 d ω ⌊T⌋₊) ps ∧
              ((MinSumFPT.run P n k ε 0 d ω ⌊T⌋₊).work : ℝ) ≤ T ∧
              (ps.length : ℝ) ≤ (n : ℝ) ^ (2 * cmax ε / ε ^ 4) ∧
              ∀ q ∈ ps, q.S0.length ≤ k ∧ 0 ≤ q.θ ∧ q.θ ≤ 1 ∧
                CoversL d q.S1 (Finset.univ.filter (fun p => ∀ B ∈ q.S0, p ∉ B.pts d)) ∧
                CoversL d q.S2 (Finset.univ.filter (fun p => ∀ B ∈ q.S0, p ∉ B.pts d)) ∧
                q.θ * q.S1.length + (1 - q.θ) * q.S2.length ≤ (k : ℝ) - q.S0.length) ∧
          MeasurableSet E ∧
          ENNReal.ofReal (1 - 1 / (N : ℝ)) ≤ MinSumFPT.tapeLaw E := by sorry

end MinSumRadiiPTAS.Main

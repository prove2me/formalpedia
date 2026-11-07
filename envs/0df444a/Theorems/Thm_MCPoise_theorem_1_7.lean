-- Prove2me | Theorems.Thm_MCPoise_theorem_1_7
-- name    : MCPoise.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:27.816203+00:00
-- url     : https://prove2.me/theorems/da634e94-939d-4c0e-8bb0-34fca7f6c33d
-- title:
--   Theorem 1.7 — an $(O(\log^5 k), O(\log^4 k))$-approximate partial solution covering $k/6$ pairs
-- statement:
--   **Theorem 1.7.** There are an efficient algorithm and an absolute constant $C$ such that for every instance and every certified $L$, the output is a $(C \log^5(k+1), C \log^4(k+1))$-approximate partial solution covering at least $k/6$ demand pairs.
--
--   Repeating this algorithm on the uncovered pairs for $O(\log k)$ rounds gives the main theorem.
--
--   Differences from the source:
--   - reading: an efficient, polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, polynomial in a fixed binary encoding on every input; reason: the source names no machine, and every step it describes is deterministic
--   - generalization: $L$ is the value of the optimal solution → $L$ is an input and the guarantee holds for every $L$ with a certifying subgraph; reason: an optimal solution certifies its own poise, so this contains $L = \mathrm{OPT}$; the proof uses only the certificate (p.35)
--   - reading: the printed $O(\cdot)$ in $\log k$ → the factor $\log(k+1)$ with one absolute constant; reason: $\log k$ vanishes at $k = 1$, and for $k \ge 2$ the two differ by a constant factor
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.7, p.7

import Mathlib
import Definitions.Def_MCPoise_WitnessFor
import Definitions.Def_MCPoise_IsPartialSolution
import Definitions.Def_LCPlanarSteiner_sgOf
import Definitions.Def_MCPoise_encIn

namespace MCPoise

/-- **Theorem 1.7.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.7, p.7: "There exists an efficient algorithm to find an (O(log⁵ k), O(log⁴ k))-approximate partial solution to MC poise that covers at least k/6 terminal pairs."

One machine on `(I, L)` and one absolute constant `C`: whenever `L` is certified, the output is a `(C log⁵(k+1), C log⁴(k+1))`-approximate partial solution covering a set `D′` of at least `k/6` demand indices.

**Formalization Note.** `L` is an input in binary (p.6: "we guess the value L"), and the certificate covers `L = OPT`. `log(k + 1)` replaces `log k`, which vanishes at `k = 1`. -/
theorem theorem_1_7 :
    ∃ alg : Inst × ℕ → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encLIn encOut alg) ∧
      ∃ C : ℝ, ∀ (I : Inst) (L : ℕ) (Hstar : SimpleGraph (Fin I.n)), WitnessFor I L Hstar →
        ∃ D' : Finset (Fin I.k),
          IsPartialSolution I (L : ℝ) (C * Real.log ((I.k : ℝ) + 1) ^ 5)
            (C * Real.log ((I.k : ℝ) + 1) ^ 4) (LCPlanarSteiner.sgOf I.n (alg (I, L))) D' ∧
          I.k ≤ 6 * D'.card := by sorry

end MCPoise

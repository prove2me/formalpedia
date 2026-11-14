-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_theorem_1_3_wordRAM
-- name    : KSATSingleFlip.Connect.theorem_1_3_wordRAM
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T08:01:57.186899+00:00
-- url     : https://prove2.me/theorems/40db94c4-fead-455b-8280-c5e6758431b4
-- title:
--   Model-specific word-RAM version of the looseness–rigidity theorem
-- statement:
--   This is an open, model-specific candidate for Theorem 1.3, in the explicit fixed-width word-RAM model. For sufficiently large fixed $k$, a deterministic flip program and a deterministic routing program, depending only on $k$, must work on every sparse encoding of each eligible formula. On a common set of at least $1-1/n$ solution mass, the first must produce a satisfying path reversing any requested variable within $O_k(n)$ steps and at most $32(\ln k)^5\ln n$ flips; the second must route to every satisfying target in a linear-radius Hamming ball within $O_k(n^2)$ steps and a linear number of flips. The probability event and the high-density rigidity conclusion use the density ranges of (1.5). The cited paper does not specify this particular instruction set; the result is unproved in this model.
-- source:
--   Formalization of Theorem 1.3, Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed p. 4 (PDF p. 6), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf. The source does not specify this particular RAM instruction set.

import Definitions.Def_KSATSingleFlip_Connect_RAMLooseness

open scoped Classical BigOperators
open Filter Topology

namespace KSATSingleFlip.Connect

/-- Model-specific candidate for the full Theorem 1.3: sparse-input programs
in the explicit fixed-width word-RAM model, and the rigidity conclusion. -/
theorem theorem_1_3_wordRAM :
    ∃ pathConstant : ℝ, 0 < pathConstant ∧
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∃ (flipProgram routeProgram : WordRAMProgram) (flipCost routeCost : ℕ)
        (looseRadius rigidRadius exceptionRate : ℝ),
        0 < flipCost ∧ 0 < routeCost ∧
        0 < looseRadius ∧ 0 < rigidRadius ∧ 0 < exceptionRate ∧
        ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
          ((m : ℝ) / n ≤ geometryDensity k false →
            1 - 1 / (n : ℝ) ≤ formulaProb n k m (fun F =>
              HasRAMLooseLocalGeometry F flipProgram routeProgram flipCost routeCost
                looseRadius pathConstant)) ∧
          (geometryDensity k true ≤ (m : ℝ) / n →
            (m : ℝ) / n ≤ (2 : ℝ)^k * (Real.log 2 - 1 / Real.log k) →
            1 - 1 / (n : ℝ) ≤ formulaProb n k m (fun F =>
              HasRigidGeometry (ofFormula F) (δ k) rigidRadius exceptionRate)) := by
  sorry

end KSATSingleFlip.Connect

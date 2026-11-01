-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosPrimeInputs_PrimeErrorDecay_uniform_prime_interval_error_jd
-- name    : OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:22:26.657731+00:00
-- url     : https://prove2.me/theorems/a4c0b7d9-9a87-4f30-b518-950ec71b14ac
-- title:
--   OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error` of [lean/OAI/NumberTheory/Jacobsthal/Primes/HighPrimeRemoval.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Jacobsthal/Primes/HighPrimeRemoval.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay`, with `open scoped _root_.Erdos970`, `open _root_.Set _root_.MeasureTheory _root_.Filter Asymptotics`, `open scoped Topology`, `open StrongChebyshev PrimeAbel`):
--
--   ```lean
--   theorem uniform_prime_interval_error_jd : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧
--       1 < a₀ ∧ 1 ≤ Real.log a₀ ∧
--       ∀ a b : ℝ, a₀ ≤ a → a ≤ b →
--         |reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤ C * decay c a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.ErdosPrimeInputs.PrimeAbel.reciprocalPrimes` and `OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.decay` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proofs of `OAI.TwoPointCorrelations.halasz_prime_mean_square_cauchy_jd` and `OAI.TwoPointCorrelations.halasz_prime_window_middle_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Jacobsthal/Primes/HighPrimeRemoval.lean (declaration OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay.uniform_prime_interval_error)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace ErdosPrimeInputs.PrimeErrorDecay

open _root_.Set _root_.MeasureTheory _root_.Filter Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel

theorem uniform_prime_interval_error_jd : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧
    1 < a₀ ∧ 1 ≤ Real.log a₀ ∧
    ∀ a b : ℝ, a₀ ≤ a → a ≤ b →
      |reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤ C * decay c a := by
  sorry

end ErdosPrimeInputs.PrimeErrorDecay

end Erdos970

end OAI
end

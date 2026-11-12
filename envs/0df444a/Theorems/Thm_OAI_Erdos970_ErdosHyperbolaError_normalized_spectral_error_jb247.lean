-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosHyperbolaError_normalized_spectral_error_jb247
-- name    : OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:43:15.475211+00:00
-- url     : https://prove2.me/theorems/a64fa843-f6dd-4603-bf70-1a16abd6cbae
-- title:
--   OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error` of [lean/OAI/NumberTheory/Jacobsthal/Harmonic/NormalizedSpectralError.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Harmonic/NormalizedSpectralError.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosHyperbolaError`, with `open scoped BigOperators`, `open ErdosHyperbolaIdentities`):
--
--   ```lean
--   theorem normalized_spectral_error_jb247 (H T : ℕ) [NeZero H] [NeZero T]
--       (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
--       (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
--       (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T)) :
--       ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
--         spectralTerm H T a c P Q 0 0‖/((H*T : ℕ) : ℝ)^2 ≤
--         8*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.ErdosHyperbolaError.errorBase`, `OAI.Erdos970.ErdosHyperbolaError.intervalLength`, `OAI.Erdos970.ErdosHyperbolaError.spectralTerm` and `OAI.Erdos970.ErdosHyperbolaIdentities.ProgressionInterval` (definitions bundle `OAIQ247J003` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Harmonic/NormalizedSpectralError.lean (declaration OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error)

import Mathlib
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Definitions.Def_OAIQ247J003

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem normalized_spectral_error_jb247 (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T)) :
    ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
      spectralTerm H T a c P Q 0 0‖/((H*T : ℕ) : ℝ)^2 ≤
      8*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  sorry

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

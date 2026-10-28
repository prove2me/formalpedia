-- Prove2me | Theorems.Thm_OAI_PiExponent_localIsolatedBezout_q68
-- name    : OAI.PiExponent.localIsolatedBezout_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:13:07.703775+00:00
-- url     : https://prove2.me/theorems/a0704679-d70d-4519-9680-fb1abdbd371f
-- title:
--   OAI.PiExponent.localIsolatedBezout_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.localIsolatedBezout` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalBezout.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalBezout.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent`):
--
--   ```lean
--   theorem localIsolatedBezout_q68
--       (k : Type) [Field k] [Infinite k] (n : ℕ)
--       {J : Type*} (f : J → MvPolynomial (Fin n) k) (D h : ℕ)
--       (hdegree : ∀ j, (f j).totalDegree ≤ D)
--       (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
--       (hminimal : P ∈ (Ideal.span (Set.range f)).minimalPrimes)
--       (hheight : P.height = (h : ℕ∞)) (hbound : h ≤ n) :
--       Module.length (Localization.AtPrime P)
--         (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
--           (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
--         ((D ^ h : ℕ) : ℕ∞)
--   ```
--
--   **Used by.** The proof of `OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalBezout.lean (declaration OAI.PiExponent.localIsolatedBezout)

import Mathlib
import Lean.Elab.Tactic.Omega

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

theorem localIsolatedBezout_q68
    (k : Type) [Field k] [Infinite k] (n : ℕ)
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (D h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ D)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hminimal : P ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (hheight : P.height = (h : ℕ∞)) (hbound : h ≤ n) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ h : ℕ) : ℕ∞) := by
  sorry

end PiExponent

end OAI
end

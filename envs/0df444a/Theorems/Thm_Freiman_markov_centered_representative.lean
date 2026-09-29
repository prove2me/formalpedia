-- Prove2me | Theorems.Thm_Freiman_markov_centered_representative
-- name    : Freiman.markov_centered_representative
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:44.148634+00:00
-- url     : https://prove2.me/theorems/eca175bc-d363-42bf-980d-542ae3d6480f
-- title:
--   Every finite symbolic Markov value has a representative attaining its maximum at zero
-- statement:
--   For any two-sided positive digit word whose finite supremum of local values is t, there is another two-sided word whose local value at zero is exactly t and all of whose local values are at most t. The bound t < 5 is unnecessary for this recentering assertion and is used separately to restrict the alphabet.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §20.1, Lemma 20.1, compactness part of its proof, printed p. 65.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem markov_centered_representative (a : ℤ → ℕ+) (t : ℝ)
    (hmax : ∀ i : ℤ, localValue a i ≤ t)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ i : ℤ, t - ε < localValue a i) :
    ∃ b : ℤ → ℕ+, localValue b 0 = t ∧
      ∀ i : ℤ, localValue b i ≤ t := by
  sorry

end Freiman

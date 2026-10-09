-- Prove2me | Theorems.Thm_OAI_Erdos3_no_interval_invariant_of_descent
-- name    : OAI.Erdos3.no_interval_invariant_of_descent
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T02:05:55.819367+00:00
-- url     : https://prove2.me/theorems/91333ae8-d168-4ecc-b641-96d474073ad6
-- title:
--   A descending invariant on progression-free intervals can hold for none of them
-- statement:
--   Let $k$ be a natural number and $T$, $C_{\min}$ real numbers. An `APFreeInterval k` $S$ is OpenAI's structure of a length $\ell = S.\mathrm{length} > 1$ and a nonempty finite set of naturals contained in $\{0, \dots, \ell - 1\}$ that is `APFree` for $k$ (contains no $k$-term arithmetic progression, in OpenAI's sense `¬ HasAP`); its parameter $S.\mathrm{parameter}$ is `densityParameter` of its density, i.e. $\max(2, \log(2/\alpha))$ where $\alpha$ = `intervalDensity` $\ell$ (points) $= |\mathrm{points}|/\ell$. Then there exists a real $C_0$ with $C_{\min} \le C_0$ and $0 \le C_0$ such that for all real $A, \beta$ with $0 \le A$ the following holds: if for every `APFreeInterval k` $S$ with $A\,(S.\mathrm{parameter})^\beta + C_0 \le \log\log S.\mathrm{length}$ and $T < S.\mathrm{parameter}$ there is an `APFreeInterval k` $S'$ with $A\,(S'.\mathrm{parameter})^\beta + C_0 \le \log\log S'.\mathrm{length}$ and $S'.\mathrm{parameter} + 1 \le S.\mathrm{parameter}$, then no `APFreeInterval k` $S$ satisfies $A\,(S.\mathrm{parameter})^\beta + C_0 \le \log\log S.\mathrm{length}$. (Here $x^\beta$ is the real power `Real.rpow`.)
--
--   Lean: `OAI.Erdos3.no_interval_invariant_of_descent` in `lean/OAI/Combinatorics/Progressions/Probability/RelativeSourceDensityParameter.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B109` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/RelativeSourceDensityParameter.lean#L431

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B109

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open Filter

end Erdos3

end

section

namespace Erdos3.FixedDensity

end Erdos3.FixedDensity

namespace Erdos3

open FixedDensity

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace APFreeInterval

variable {k : ℕ}

end APFreeInterval

theorem no_interval_invariant_of_descent (k : ℕ) (T Cmin : ℝ) :
    ∃ C₀ : ℝ, Cmin ≤ C₀ ∧ 0 ≤ C₀ ∧ ∀ A β : ℝ, 0 ≤ A →
      (∀ S : APFreeInterval k, A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length) →
        T < S.parameter → ∃ S' : APFreeInterval k,
          A * S'.parameter ^ β + C₀ ≤ Real.log (Real.log S'.length) ∧
          S'.parameter + 1 ≤ S.parameter) →
      ∀ S : APFreeInterval k, ¬ A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length) := by
  sorry

end Erdos3
end
end OAI

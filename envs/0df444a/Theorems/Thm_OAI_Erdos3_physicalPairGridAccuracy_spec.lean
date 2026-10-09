-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalPairGridAccuracy_spec
-- name    : OAI.Erdos3.physicalPairGridAccuracy_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:48:58.016498+00:00
-- url     : https://prove2.me/theorems/cbe3a333-369e-4589-96d8-d0e1d53ee9b0
-- title:
--   The physical pair grid accuracy lies in (0, 1] and meets its epsilon budget
-- statement:
--   Let $J$ be a finite type with decidable equality, $n \in \mathbb{N}$, $k \in J$, and $C, \kappa, A, \varepsilon$ real numbers with $0 \le A$ and $0 < \varepsilon$. Write $\rho = $ `physicalPairGridAccuracy n k C κ A ε`, OpenAI's real number given by `residualGridAccuracy` applied to $A^{2n}$, $2^n$, `smoothPairKernelLip n k C κ` and $\varepsilon$, where `smoothPairKernelLip n k C κ` is an explicit $\mathbb{R}_{\ge 0}$-valued Lipschitz constant of OpenAI. Then $0 < \rho \le 1$ and
--   $$6\, A^{2n}\, 2^{n}\, \texttt{smoothPairKernelLip}\ n\ k\ C\ \kappa \cdot \rho \le \varepsilon.$$
--
--   Lean: `OAI.Erdos3.physicalPairGridAccuracy_spec` in `lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean#L355

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem physicalPairGridAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    0 < rho ∧ rho ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * (smoothPairKernelLip n k C κ : ℝ) * rho ≤ epsilon := by
  sorry

end Erdos3
end
end OAI

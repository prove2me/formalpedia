-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalResidualPairBudget_of_accuracies
-- name    : OAI.Erdos3.physicalResidualPairBudget_of_accuracies
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:25:45.017216+00:00
-- url     : https://prove2.me/theorems/0d62eb9d-bc1c-403a-9e67-772866e74ca0
-- title:
--   At the chosen accuracies the physical residual pair budget is at most epsilon
-- statement:
--   Let $I$ and $J$ be finite types with decidable equality, and let $\mathrm{lo} : I \to \mathbb{Z}$, $N : I \to \mathbb{N}$ and $H : I \to \mathbb{R}$ with $H_i > 0$ for every $i$; let $k \in J$, $Q \in \mathbb{N}$, $C, \kappa \in \mathbb{R}$, $\mathrm{degree} \in \mathbb{N}$, and $A, \varepsilon$ real numbers with $0 \le A$, $0 < \varepsilon$ and $N_i \le A H_i$ for every $i$. Write $n = |I|$ and put $\delta = $ `physicalPairPointAccuracy n k Q C κ A ε`, $\rho = $ `physicalPairGridAccuracy n k C κ A ε` and $\eta = $ `physicalPairMeanAccuracy n k Q C κ A degree ε` (OpenAI's explicit real-valued accuracies). Then
--   $$\texttt{physicalResidualPairBudget}\ \mathrm{lo}\ N\ H\ k\ Q\ C\ \kappa\ \delta\ \mathrm{degree}\ \eta\ \rho \le \varepsilon,$$
--   where `physicalResidualPairBudget` is OpenAI's real-valued quantity $\dfrac{|B|^2}{\prod_i H_i^2}\Bigl(K\,(\eta\, c)^2 + (E_\delta + \Lambda \rho)\, 2^{n} (1 + \eta\, c^2)\Bigr)$, with $B = $ `translatedIntegerBox lo N` (the box $\{\mathrm{lo} + y : 0 \le y_i < N_i\}$), $K = $ `smoothPairKernelCap n k C κ`, $c = $ `residueTruncationCap (BoundedPrime Q) degree η`, $E_\delta = $ `fullSmoothPairError n k Q C κ δ` and $\Lambda = $ `smoothPairKernelLip n k C κ` (explicit constants of OpenAI).
--
--   Lean: `OAI.Erdos3.physicalResidualPairBudget_of_accuracies` in `lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PhysicalPairAccuracyLogBounds.lean#L370

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

theorem physicalResidualPairBudget_of_accuracies {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i) (k : J) (Q : ℕ)
    (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    let delta := physicalPairPointAccuracy (Fintype.card I) k Q C κ A epsilon
    let rho := physicalPairGridAccuracy (Fintype.card I) k C κ A epsilon
    let eta := physicalPairMeanAccuracy (Fintype.card I) k Q C κ A degree epsilon
    physicalResidualPairBudget lo N H k Q C κ delta degree eta rho ≤ epsilon := by
  sorry

end Erdos3
end
end OAI

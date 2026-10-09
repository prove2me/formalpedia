-- Prove2me | Theorems.Thm_OAI_Erdos3_replacement_selected_parameter_bounds
-- name    : OAI.Erdos3.replacement_selected_parameter_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:23:14.531557+00:00
-- url     : https://prove2.me/theorems/4d25845a-571a-4bd7-a8a1-9aa6d0128536
-- title:
--   The selected replacement parameters are bounded by e to the common input logarithm
-- statement:
--   Let $m, n, d, D$ be natural numbers and $K, A, C_w, c, \varepsilon, P$ real numbers with $0 \le P$, $0 \le K$, $0 \le A$, $0 \le C_w$, $0 < c$, $0 < \varepsilon$, $0 < D$, $D \le e^{P}$, $K \le e^{P}$, $A \le e^{P}$, $C_w \le e^{P}$, $c^{-1} \le e^{P}$ and $\varepsilon^{-1} \le e^{P}$. Put $\tau = $ `weightedReplacementTolerance ((3K)^m) (2^(n+1) A^n) ε`, where `weightedReplacementTolerance F E ε` $= \min\bigl(1, \varepsilon^2/(1 + F^2(1 + E))\bigr)$, and $Z = $ `replacementCommonInputLog m n d P` (an explicit real-valued function of OpenAI). Then:
--
--   - $0 < \tau$ and $\tau^{-1} \le e^{Z}$;
--   - $0 < g$ and $g^{-1} \le e^{Z}$, where $g = $ `integerBoxRetainedGap d D c τ` $= D \cdot \texttt{integerBoxNearRatio}\ d\ \tau \cdot c$ and `integerBoxNearRatio d τ` $= \min\bigl(1, \tau/(1 + 2 \cdot 3^d)\bigr)$;
--   - $D \cdot G \le e^{Z}$, where $G = $ `integerBoxGcdCutoff d C_w τ` $= \lceil 2 \cdot 2^{d-1}(1 + C_w)/\tau \rceil + 1$ (a natural number; the product is cast to $\mathbb{R}$);
--   - `integerBoxPairScale d C_w τ` $= \max\bigl(G, 1/\texttt{integerBoxNearRatio}\ d\ \tau\bigr) \le e^{Z}$.
--
--   Lean: `OAI.Erdos3.replacement_selected_parameter_bounds` in `lean/OAI/Combinatorics/Progressions/Dynamics/InitialBudgetJointReplacement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/InitialBudgetJointReplacement.lean#L95

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

theorem replacement_selected_parameter_bounds (m n d D : ℕ) {K A Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hCwidth : Cwidth ≤ Real.exp P) (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let Z := replacementCommonInputLog m n d P
    0 < tol ∧ tol⁻¹ ≤ Real.exp Z ∧
    0 < integerBoxRetainedGap d D c tol ∧ (integerBoxRetainedGap d D c tol)⁻¹ ≤ Real.exp Z ∧
    ((D * integerBoxGcdCutoff d Cwidth tol : ℕ) : ℝ) ≤ Real.exp Z ∧
    integerBoxPairScale d Cwidth tol ≤ Real.exp Z := by
  sorry

end Erdos3
end
end OAI

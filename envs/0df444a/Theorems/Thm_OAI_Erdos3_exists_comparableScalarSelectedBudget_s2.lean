-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_comparableScalarSelectedBudget_s2
-- name    : OAI.Erdos3.exists_comparableScalarSelectedBudget_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:34:06.15797+00:00
-- url     : https://prove2.me/theorems/e9e979ee-e8bc-4fa2-b758-97b01d53ac4d
-- title:
--   Existence of constants making the scalar selected budget comparable to a power of p
-- statement:
--   Let $E, d, r$ be natural numbers with $E \ge 2$, $d \ge 2$, $r \ge 2$, and let $\varepsilon$ be a real number with $0 < \varepsilon \le 1$. Then there exist natural numbers $A \ge 3$, $C \ge 2$, $F \ge 2$ such that the following holds for every natural number $n$ and all reals $p, \sigma$ with $p \ge 2$, $n \le p$, $\sigma > 0$ and $\sigma^{-1} \le e^p$.
--
--   Put $D = rd$, $\mathrm{target} = 8(D + 1)(p + 1)$, $P_0 = A(\mathrm{target} + 1)$, $\mathrm{budget} = (\mathrm{target} + 2)^C$, and $\tau$ = `unconditionedSpatialTrimFraction n σ` $= \sigma / (32(n+1))$ (defined by OpenAI). Then all of the following hold:
--   - $p \le \mathrm{target}$, $2 \le \mathrm{target}$, $n \le \mathrm{target}$, and $4(dn + 1) \le \mathrm{target}$;
--   - $0 \le P_0$ and $3\,\mathrm{target} + 10 \le P_0$;
--   - $\varepsilon^{-1} \le e^{P_0}$; `probabilityProfileLipschitz` $\le e^{P_0}$ (a constant of OpenAI); $D \le e^{P_0}$; $d \le e^{P_0}$; $r + 1 \le e^{P_0}$; $2 \le e^{P_0}$; $\tau^{-1} \le e^{P_0}$; and $16(2D + 1)/\tau \le e^{P_0}$;
--   - $0 \le \mathrm{budget}$, and `scalarInitialThreshold E ((d + 1) * n) n d ε target P₀` $\le \mathrm{budget}$, where `scalarInitialThreshold` is an explicit real-valued function defined by OpenAI;
--   - $(D + 4)(\mathrm{budget} + P_0 + 20) \le (p + F)^F$ and $\mathrm{budget} \le (p + F)^F$.
--
--   Lean: `OAI.Erdos3.exists_comparableScalarSelectedBudget_s2`, which states OpenAI's `OAI.Erdos3.exists_comparableScalarSelectedBudget` (in `lean/OAI/Combinatorics/Progressions/Dynamics/ComparableScalarSelectedBudget.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B086` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/ComparableScalarSelectedBudget.lean (declaration OAI.Erdos3.exists_comparableScalarSelectedBudget)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B086

section

namespace OAI

section

namespace Erdos3

theorem exists_comparableScalarSelectedBudget_s2 (E d r : ℕ)
    (hE : 2 ≤ E) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ (n : ℕ) {p σ : ℝ}, 2 ≤ p → (n : ℝ) ≤ p →
      0 < σ → σ⁻¹ ≤ Real.exp p →
    let D := r * d
    let target := 8 * ((D : ℝ) + 1) * (p + 1)
    let P0 := (A : ℝ) * (target + 1)
    let budget := (target + 2) ^ C
    let τ := unconditionedSpatialTrimFraction n σ
    p ≤ target ∧ 2 ≤ target ∧ (n : ℝ) ≤ target ∧
      4 * ((d : ℝ) * n + 1) ≤ target ∧
      0 ≤ P0 ∧ 3 * target + 10 ≤ P0 ∧
      epsilon⁻¹ ≤ Real.exp P0 ∧
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 ∧
      (D : ℝ) ≤ Real.exp P0 ∧ (d : ℝ) ≤ Real.exp P0 ∧
      (r : ℝ) + 1 ≤ Real.exp P0 ∧ 2 ≤ Real.exp P0 ∧
      τ⁻¹ ≤ Real.exp P0 ∧ 16 * (2 * (D : ℝ) + 1) / τ ≤ Real.exp P0 ∧
      0 ≤ budget ∧
      scalarInitialThreshold E ((d + 1) * n) n d epsilon target P0 ≤ budget ∧
      ((D : ℝ) + 4) * (budget + P0 + 20) ≤ (p + F) ^ F ∧
      budget ≤ (p + F) ^ F := by
  sorry

end Erdos3

end

end OAI
end

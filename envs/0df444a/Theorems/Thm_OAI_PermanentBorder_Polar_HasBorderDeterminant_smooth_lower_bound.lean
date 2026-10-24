-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_HasBorderDeterminant_smooth_lower_bound
-- name    : OAI.PermanentBorder.Polar.HasBorderDeterminant.smooth_lower_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:51:53.259443+00:00
-- url     : https://prove2.me/theorems/df90fc68-872c-4875-9452-45353d9beaaf
-- title:
--   A smooth homogeneous form of degree r in d variables needs border determinantal size at least (r − 1)(d − 1)/(4e) (OpenAI permanent, Theorem 2.3)
-- statement:
--   **The statement.** Let $\sigma$ be a finite set of $d \ge 2$ variables, $r \ge 2$, and $f \in \mathbb C[x_\sigma]$ homogeneous of degree $r$ whose only common zero with all its partial derivatives is $y = 0$ (its zero set in $\mathbb P^{d-1}$ is smooth). If $f$ has a border determinantal representation of size $n$, then
--   $$\frac{(r-1)(d-1)}{4e} \;\le\; n.$$
--
--   This is the Lean form of the paper's Theorem 2.3 (lower bound for smooth homogeneous forms), stated for border representations.
--
--   Lean: `OAI.PermanentBorder.Polar.HasBorderDeterminant.smooth_lower_bound`, OpenAI's theorem of that name (in `lean/OAI/Algebra/Determinantal/BorderPolars.lean`).
-- source:
--   OpenAI, A cubic lower bound for border determinantal complexity of the permanent, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 108; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf, Theorem 2.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Determinantal/BorderPolars.lean (declaration OAI.PermanentBorder.Polar.HasBorderDeterminant.smooth_lower_bound)

import Mathlib
import Definitions.Def_PermanentCubic

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder
open MvPolynomial
open scoped Classical

namespace Polar

theorem HasBorderDeterminant.smooth_lower_bound {σ : Type} [Fintype σ]
    {n r : ℕ} {f : Poly σ} (hb : HasBorderDeterminant n f)
    (hσ : 2 ≤ Fintype.card σ) (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : σ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ((r-1 : ℕ) : ℝ) * ((Fintype.card σ-1 : ℕ) : ℝ) / (4*Real.exp 1) ≤ n := by
  sorry
end Polar
end PermanentBorder

end OAI
end

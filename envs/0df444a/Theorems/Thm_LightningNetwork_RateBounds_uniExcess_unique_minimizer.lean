-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_uniExcess_unique_minimizer
-- name    : LightningNetwork.RateBounds.uniExcess_unique_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:49:14.975633+00:00
-- url     : https://prove2.me/theorems/70a588e2-70b4-4339-8db8-502f40a7594f
-- title:
--   Proof of Theorem 2(i): $F$ has the unique minimizer $\hat m = \cosh^{-1}(B\kappa/2+1)/\kappa$, with the printed minimum
-- statement:
--   Let $B > 0$, $\kappa > 0$, $C \in \mathbb R$, $F(m) = C/(1-e^\kappa) + B/(e^{\kappa m}-1) + m$ and
--
--   $$
--   \hat m = \frac{\cosh^{-1}\!\left(\frac{B\kappa}{2} + 1\right)}{\kappa}.
--   $$
--
--   Then
--
--   1. for every $m > 0$, $F'(m) = \dfrac{B\kappa}{2 - 2\cosh(\kappa m)} + 1$;
--   2. $\hat m > 0$ and it satisfies the first-order condition $\dfrac{B\kappa}{2 - 2\cosh(\kappa \hat m)} + 1 = 0$;
--   3. $F(\hat m) < F(m)$ for every $m > 0$ with $m \ne \hat m$;
--   4. $$F(\hat m) = \frac{C}{1-e^\kappa} + \frac{2B}{B\kappa + \sqrt{B\kappa(B\kappa+4)}} + \frac{\cosh^{-1}\!\left(\frac{B\kappa}{2}+1\right)}{\kappa}.$$
--
--   A unidirectional channel is cheaper than on-chain settlement for some size exactly when $F(\hat m) < 0$.
--
--   Differences from the source:
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
--   - generalization: C > 0 (the cost of an on-chain transaction) → C any real number; reason: C enters F only as an additive constant: the minimizer does not depend on C and the formula for F(m̂) holds for every C
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), unnumbered step, p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniExcess

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(i), unnumbered step: the unique minimizer of F and its value.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), p. 11: "Thus, the function admits a unique minimum for
m̂ ∈ (0, ∞), and such minimum satisfies the first-order condition F′(m̂) = 0, that is,
Bκ/(2 − 2cosh(κm)) + 1 = 0 which yields m̂ = cosh⁻¹(Bκ/2 + 1)/κ and
F(m̂) = C/(1 − e^κ) + 2B/(Bκ + √(Bκ(Bκ + 4))) + cosh⁻¹(Bκ/2 + 1)/κ."

For `0 < B`, `0 < κ` and any `C`, with `m̂ = arcosh(Bκ/2 + 1)/κ`:
1. `F'(m) = Bκ/(2 − 2 cosh(κm)) + 1` for every `m > 0`;
2. `m̂ > 0` and `Bκ/(2 − 2 cosh(κm̂)) + 1 = 0`;
3. `F(m̂) < F(m)` for every `m > 0`, `m ≠ m̂` (unique minimizer on `(0, ∞)`);
4. `F(m̂) = C/(1 − e^κ) + 2B/(Bκ + √(Bκ(Bκ + 4))) + arcosh(Bκ/2 + 1)/κ`.

**Formalization Note.** `cosh⁻¹` is `Real.arcosh`, which is the inverse of `cosh` on `[1, ∞)`. -/
theorem uniExcess_unique_minimizer (κ B C : ℝ) (hB : 0 < B) (hκ : 0 < κ) :
    let mhat := Real.arcosh (B * κ / 2 + 1) / κ
    (∀ m : ℝ, 0 < m →
        HasDerivAt (uniExcess κ B C) (B * κ / (2 - 2 * Real.cosh (κ * m)) + 1) m) ∧
      0 < mhat ∧
      B * κ / (2 - 2 * Real.cosh (κ * mhat)) + 1 = 0 ∧
      (∀ m : ℝ, 0 < m → m ≠ mhat → uniExcess κ B C mhat < uniExcess κ B C m) ∧
      uniExcess κ B C mhat = C / (1 - Real.exp κ)
        + 2 * B / (B * κ + Real.sqrt (B * κ * (B * κ + 4)))
        + Real.arcosh (B * κ / 2 + 1) / κ := by sorry

end LightningNetwork.RateBounds

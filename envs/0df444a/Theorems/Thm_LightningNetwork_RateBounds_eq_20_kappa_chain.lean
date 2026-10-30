-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_20_kappa_chain
-- name    : LightningNetwork.RateBounds.eq_20_kappa_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:51:29.75644+00:00
-- url     : https://prove2.me/theorems/55a222f8-2415-406c-9842-107056cf53f5
-- title:
--   Eq. (20): $\kappa \ge (e^C-1)/B \ge C/B \ge \alpha^2/(B(1-\alpha))$, whence $F(\hat m) \ge 0$
-- statement:
--   Let $B > 0$, $C > 0$, $0 < \alpha \le C/(C+1)$, and suppose $\kappa \ge (e^C - 1)/B$. Then
--
--   1. $\kappa \ge \dfrac2B\bigl(\cosh(C-\alpha) - 1\bigr)$;
--   2. $\dfrac{e^C - 1}{B} \ge \dfrac CB \ge \dfrac{\alpha^2}{B(1-\alpha)}$;
--   3. with $\hat m = \cosh^{-1}(B\kappa/2+1)/\kappa$ and $F(m) = C/(1-e^\kappa) + B/(e^{\kappa m}-1) + m$, $F(\hat m) \ge 0$.
--
--   With $\kappa = \log(1 + r/\lambda)$, the condition $\kappa \ge (e^C-1)/B$ is $C \le \log(1 + B\log(1 + r/\lambda))$, the negation of the bound (5) of Theorem 2(i).
--
--   Differences from the source:
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (20), p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniExcess

namespace LightningNetwork.RateBounds

/-- **The chain (20) and its consequence F(m̂) ≥ 0.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (20), p. 11: "Thus, if κ ≥ (e^C − 1)/B, then
κ ≥ (2/B)(cosh(C − α) − 1) and, choosing α ≤ C/(C+1), κ ≥ (e^C − 1)/B ≥ C/B ≥ α²/(B(1 − α))
whence F(m̂) ≥ 0 by (17)."

For `B > 0`, `C > 0`, `0 < α ≤ C/(C + 1)` and `κ ≥ (e^C − 1)/B`:
1. `κ ≥ (2/B)(cosh(C − α) − 1)`;
2. `(e^C − 1)/B ≥ C/B ≥ α²/(B(1 − α))`;
3. with `m̂ = arcosh(Bκ/2 + 1)/κ`, `F(m̂) ≥ 0`.

**Formalization Note.** `α ≤ C/(C + 1) < 1`, so `1 − α > 0`. -/
theorem eq_20_kappa_chain (B C α κ : ℝ) (hB : 0 < B) (hC : 0 < C) (hα0 : 0 < α)
    (hαC : α ≤ C / (C + 1)) (hκ : (Real.exp C - 1) / B ≤ κ) :
    2 / B * (Real.cosh (C - α) - 1) ≤ κ ∧
      C / B ≤ (Real.exp C - 1) / B ∧
      α ^ 2 / (B * (1 - α)) ≤ C / B ∧
      0 ≤ uniExcess κ B C (Real.arcosh (B * κ / 2 + 1) / κ) := by sorry

end LightningNetwork.RateBounds

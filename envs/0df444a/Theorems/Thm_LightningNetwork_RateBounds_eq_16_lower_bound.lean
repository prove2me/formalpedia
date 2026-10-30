-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_16_lower_bound
-- name    : LightningNetwork.RateBounds.eq_16_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:49:27.658308+00:00
-- url     : https://prove2.me/theorems/538353b4-90b5-40e2-b4b9-9a2deb03fb8e
-- title:
--   Eq. (16): $2B/(B\kappa + \sqrt{B\kappa(B\kappa+4)}) \ge \alpha/\kappa$, with the estimate $C/(1-e^\kappa) > -C/\kappa$
-- statement:
--   Let $C > 0$ (on-chain cost), $B > 0$ (reset cost) and $0 < \alpha < 1$. Then
--
--   1. for every $\kappa' > 0$, $\dfrac{C}{1 - e^{\kappa'}} > -\dfrac{C}{\kappa'}$ (from $e^x > 1 + x$);
--   2. if $\kappa \ge \dfrac{\alpha^2}{B(1-\alpha)}$, then
--   $$
--   \frac{2B}{B\kappa + \sqrt{B\kappa(B\kappa + 4)}} \;\ge\; \frac{\alpha}{\kappa}.
--   $$
--
--   These lower-bound the first two terms of the minimum $F(\hat m)$ in the proof of Theorem 2(i).
--
--   Differences from the source: none.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (16) and the sentence before it, p. 11

import Mathlib

namespace LightningNetwork.RateBounds

/-- **Inequality (16), with the elementary estimate that precedes it.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (16), p. 11: "For this purpose, note first
that the elementary estimate e^x > 1 + x for x > 0 implies that C/(1 − e^κ) > −C/κ for all κ > 0.
Note also that 2B/(Bκ + √(Bκ(Bκ + 4))) ≥ α/κ for κ ≥ α²/(B(1 − α)), 0 < α < 1."

For an on-chain cost `C > 0`, a reset cost `B > 0` and `0 < α < 1`:
1. `C/(1 − e^κ') > −C/κ'` for every `κ' > 0`;
2. if `κ ≥ α²/(B(1 − α))` then `2B/(Bκ + √(Bκ(Bκ + 4))) ≥ α/κ`.

**Formalization Note.** `C > 0` is the model's (C is the cost of an on-chain transaction); the
estimate uses it. In clause 2, `κ > 0` follows from the hypotheses. -/
theorem eq_16_lower_bound (B C α κ : ℝ) (hB : 0 < B) (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1)
    (hκ : α ^ 2 / (B * (1 - α)) ≤ κ) :
    (∀ κ' : ℝ, 0 < κ' → -C / κ' < C / (1 - Real.exp κ')) ∧
      α / κ ≤ 2 * B / (B * κ + Real.sqrt (B * κ * (B * κ + 4))) := by sorry

end LightningNetwork.RateBounds

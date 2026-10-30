-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_piL_deriv_and_monotonicity
-- name    : MarketplaceLeakage.Communication.piL_deriv_and_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:05:08.091925+00:00
-- url     : https://prove2.me/theorems/a062d669-b88b-455c-8991-8569e85301fb
-- title:
--   $d\Pi_L/d\eta$; $\Pi_L$ strictly decreasing and $\Pi_H$ strictly increasing when $qv>c$
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Let $0<c<v$, $0<q<1$ and $qv>c$. Then:
--
--   1. at every $\eta\ne1$,
--   $$
--   \frac{d\Pi_L}{d\eta}=-\frac{(1-q)\,qv}{(1-\eta)^2}\Bigl((2-\eta)q\eta+2(1-\eta)^2\Bigr)+c(1-q);
--   $$
--   2. $(2-\eta)q\eta+2(1-\eta)^2>(1-\eta)^2$ for every $\eta\in[0,1)$;
--   3. the derivative is negative on $[0,1)$;
--   4. $\Pi_L$ is strictly decreasing on $[0,1)$ and $\Pi_H$ is strictly increasing.
--
--   Together with the endpoint values these give a unique crossing point of $\Pi_H$ and $\Pi_L$.
--
--   Differences from the source:
--
--   - encoding: the inequality, sign and monotonicity of Π_L for η in the model's [0, 1] → on [0, 1); reason: Π_L is undefined at η = 1
--   - generalization: the derivative formula (for η in the model's range) → at every η ≠ 1; reason: Π_L is a rational function of η with its only pole at 1; specializes to [0, 1)
--   - generalization: "Π_H is obviously increasing in η" → Π_H strictly increasing on all of ℝ; reason: Π_H is linear in η with slope q(v − c) > 0; specializes to [0, 1]
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §8.4 (proof of Proposition 3), unnumbered display, p. 38

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_piH
import Definitions.Def_MarketplaceLeakage_Communication_piL

namespace MarketplaceLeakage.Communication

/-- **`dΠ_L/dη`; `Π_H` increasing and `Π_L` decreasing when `qv > c`.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §8.4 (proof of Proposition 3), unnumbered display, p. 38: "Furthermore, ΠH is obviously
increasing in η and ΠL is decreasing in η:
dΠL/dη = −(1 − q) qv/(1 − η)² ((2 − η) qη + 2 (1 − η)²) + c (1 − q),
which is negative under qv > c since (2 − η) qη + 2 (1 − η)² > (1 − η)²."

Standing assumptions `0 < c < v` (pp. 5–6), `0 < q < 1` (p. 14), and `qv > c`
("Suppose now qv > c", p. 38). Then
(1) the derivative formula holds at every `η ≠ 1`;
(2) `(2 − η)qη + 2(1 − η)² > (1 − η)²` for every `η ∈ [0, 1)`;
(3) the derivative is negative on `[0, 1)`;
(4) `Π_L` is strictly decreasing on `[0, 1)` and `Π_H` is strictly increasing.

**Formalization Note.** `Π_L` is undefined at `η = 1`, so (2)–(4) range over `[0, 1)`;
(1) holds at every `η ≠ 1` and (4) for `Π_H` on all of `ℝ`. -/
theorem piL_deriv_and_monotonicity {q v c : ℝ} (hc : 0 < c) (hcv : c < v) (hq0 : 0 < q)
    (hq1 : q < 1) (hqv : c < q * v) :
    (∀ η : ℝ, η ≠ 1 → HasDerivAt (piL q v c)
        (-(1 - q) * q * v / (1 - η) ^ 2 * ((2 - η) * q * η + 2 * (1 - η) ^ 2) + c * (1 - q)) η) ∧
      (∀ η : ℝ, 0 ≤ η → η < 1 → (1 - η) ^ 2 < (2 - η) * q * η + 2 * (1 - η) ^ 2) ∧
      (∀ η : ℝ, 0 ≤ η → η < 1 →
        -(1 - q) * q * v / (1 - η) ^ 2 * ((2 - η) * q * η + 2 * (1 - η) ^ 2) + c * (1 - q) < 0) ∧
      StrictAntiOn (piL q v c) (Set.Ico 0 1) ∧ StrictMono (piH q v c) := by sorry

end MarketplaceLeakage.Communication

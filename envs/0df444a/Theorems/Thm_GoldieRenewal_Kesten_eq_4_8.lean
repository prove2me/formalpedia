-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_eq_4_8
-- name    : GoldieRenewal.Kesten.eq_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:12:31.988164+00:00
-- url     : https://prove2.me/theorems/a553798c-82cf-4229-b0d1-1bb52af2b358
-- title:
--   (4.8) — for κ > 1, E|R|^{κ−1} < ∞, ‖M‖_{κ−1} < 1 and ‖R‖_{κ−1} ≤ ‖Q‖_{κ−1}/(1 − ‖M‖_{κ−1})
-- statement:
--   Let $(Q,M)$ have joint law $\mu$, let $M$ satisfy the conditions of Lemma 2.2 for some $\kappa>1$, and suppose $\mathbf E|Q|^\kappa<\infty$ (4.2). Let $R$ have a law satisfying the random difference equation $R\overset{\mathcal L}{=}Q+MR$ with $R$ independent of $(Q,M)$. With the paper's $\|X\|_p = \mathbf E|X|^p$ for $0<p\le1$ and $(\mathbf E|X|^p)^{1/p}$ for $p\ge1$:
--
--   1. $\mathbf E|R|^{\kappa-1}<\infty$;
--   2. $\|M\|_{\kappa-1}<1$;
--   3. the bound
--   $$
--   \|R\|_{\kappa-1} \le \frac{\|Q\|_{\kappa-1}}{1-\|M\|_{\kappa-1}}\qquad\text{(4.8)} .
--   $$
--
--   The finiteness of $\mathbf E|R|^{\kappa-1}$ is used in the proof of Theorem 4.1, and the bound makes the estimate (4.7) for $C_++C_-$ explicit in terms of $Q$ and $M$ alone.
--
--   **Formalization Note** $\|\cdot\|_p$ is evaluated on laws: $\|R\|$ on the solution law $\rho$, $\|Q\|$ and $\|M\|$ on the marginals of $\mu$. The statement is made for every law solving (1.1); by Theorem 4.1 there is exactly one.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 137, (4.8)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **(4.8)** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 137). Under the hypotheses of Theorem 4.1 with `κ > 1`, let `ρ`
be a law for `R` satisfying (1.1). Then `E|R|^{κ−1} < ∞`, `‖M‖_{κ−1} < 1`, and
`‖R‖_{κ−1} ≤ ‖Q‖_{κ−1} / (1 − ‖M‖_{κ−1})`, where `‖X‖_p` is the paper's §1 quantity
(`E|X|^p` for `p ≤ 1`, `(E|X|^p)^{1/p}` for `p ≥ 1`).

**Formalization Note** `‖·‖_p` is `goldieNorm p` applied to the law of the variable: `ρ` for `R`,
the first marginal of `μ` for `Q`, the second for `M`. The paper's "`< ∞`" and the finiteness of
`E|R|^{κ−1}` it relies on (p. 156) are the integrability conjunct; `‖M‖_{κ−1} < 1` is part of the
content (the bound is meaningful only then). Stated for every law solving (1.1). -/
theorem eq_4_8 (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞) (hκ1 : 1 < κ)
    (ρ : ProbabilityMeasure ℝ) (hρ : rdeOperator μ (ρ : Measure ℝ) = ρ) :
    Integrable (fun r : ℝ => |r| ^ (κ - 1)) (ρ : Measure ℝ) ∧
      goldieNorm (κ - 1) (μ.map Prod.snd) < 1 ∧
      goldieNorm (κ - 1) (ρ : Measure ℝ) ≤
        goldieNorm (κ - 1) (μ.map Prod.fst) / (1 - goldieNorm (κ - 1) (μ.map Prod.snd)) := by sorry

end GoldieRenewal.Kesten

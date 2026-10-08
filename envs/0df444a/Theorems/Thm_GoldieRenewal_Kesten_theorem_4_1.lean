-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_theorem_4_1
-- name    : GoldieRenewal.Kesten.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:21.374349+00:00
-- url     : https://prove2.me/theorems/211efdb8-8d80-4afd-84ed-6368fafab0c5
-- title:
--   Theorem 4.1 — R =_L Q + MR has a unique law, t^κP(R > t) → C₊, t^κP(R < −t) → C₋ with C± from (4.3)/(4.4), and C₊ + C₋ > 0 iff (4.5)
-- statement:
--   Let $Q$ and $M$ be random variables on a common probability space, with joint law $\mu$ (no independence and no sign condition). Suppose $M$ satisfies the conditions of Lemma 2.2 for some $\kappa>0$ — $\mathbf E|M|^\kappa=1$, $\mathbf E|M|^\kappa\log^+|M|<\infty$, and $\log|M|$ given $M\neq 0$ nonarithmetic — so that $m=\mathbf E|M|^\kappa\log|M|\in(0,\infty)$, and suppose
--
--   $$
--   \mathbf E|Q|^\kappa<\infty\qquad\text{(4.2)}.
--   $$
--
--   Then:
--
--   1. there is a unique probability law for $R$ satisfying the random difference equation $R\overset{\mathcal L}{=}Q+MR$, $R$ independent of $(Q,M)$ (1.1);
--   2. for $R$ with this law, independent of $(Q,M)$, the expectations $\mathbf E\big|((Q+MR)^\pm)^\kappa-((MR)^\pm)^\kappa\big|$ are finite;
--   3. as $t\to\infty$,
--   $$
--   t^\kappa P(R>t)\to C_+,\qquad t^\kappa P(R<-t)\to C_-\qquad\text{((2.10), (2.11))},
--   $$
--   where, if $M\ge0$ a.s.,
--   $$
--   C_\pm = \frac{\mathbf E\big(((Q+MR)^\pm)^\kappa-((MR)^\pm)^\kappa\big)}{\kappa m}\qquad\text{(4.3)},
--   $$
--   and otherwise $C_+=C_-=\frac{1}{2\kappa m}\mathbf E\big(|Q+MR|^\kappa-|MR|^\kappa\big)$ (4.4);
--   4. $C_++C_->0$ if and only if (4.5): for each fixed $c\in\mathbb R$, $P(Q=(1-M)c)<1$.
--
--   Apart from the formulae for $C_\pm$ this is Kesten's (1973) Theorem 5 in dimension one: the stationary law of the affine recursion $R_n = Q_n+M_nR_{n-1}$ has power tails of exponent $\kappa$, with explicit constants, and these tails are genuinely present unless the recursion has a deterministic fixed point.
--
--   **Formalization Note** Everything is stated for laws: a law for $R$ satisfying (1.1) is a probability law $\rho$ on $\mathbb R$ equal to the law of $Q+MR$ under $\mu\otimes\rho$, and uniqueness is among all probability laws on $\mathbb R$. "$P(R>t)\sim C_+t^{-\kappa}$" is read as $t^\kappa P(R>t)\to C_+$, the paper's own reading (p. 130), which covers $C_+=0$. The expectations in (4.3)–(4.4) are integrals against $\mu\otimes\rho$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, pp. 135–136, Theorem 4.1, (4.2)–(4.5)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- **Theorem 4.1** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), pp. 135–136; Kesten (1973), Theorem 5, with explicit constants).
Let `(Q, M)` have joint law `μ` on `ℝ × ℝ`, let `M` satisfy the conditions of Lemma 2.2 for some
`κ > 0`, and suppose (4.2) `E|Q|^κ < ∞`. Then:

1. there is a unique law `ρ` for `R` satisfying (1.1), `R =_L Q + MR` with `R` independent of
   `(Q, M)` — unique among all probability laws on `ℝ`;
2. for this law the expectations in (4.3) are finite: `((Q + MR)^±)^κ − ((MR)^±)^κ` is integrable
   for `R` with law `ρ` independent of `(Q, M)`;
3. (2.10) `t^κ P(R > t) → C₊` and (2.11) `t^κ P(R < −t) → C₋` as `t → ∞`, where `C₊, C₋` are
   given by (4.3) if `M ≥ 0` a.s. and by (4.4) otherwise (`kestenCplus`, `kestenCminus`);
4. `C₊ + C₋ > 0` if and only if (4.5): for each fixed `c ∈ ℝ`, `P(Q = (1 − M)c) < 1`.

**Formalization Note** Everything is stated at the level of laws: a law for `R` satisfying (1.1)
is a probability measure `ρ` with `rdeOperator μ ρ = ρ`, and expectations involving `R` and
`(Q, M)` are integrals against `μ ⊗ ρ`. "`P(R > t) ~ C₊ t^{−κ}`" is read as
`t^κ P(R > t) → C₊`, as the paper instructs on p. 130 (this covers `C₊ = 0`). (4.2) is a lower
Lebesgue integral. The integrability of the absolute-value integrand of (4.4) follows from that of
the two one-sided integrands, which item 2 asserts. -/
theorem theorem_4_1 (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞) :
    ∃ ρ : ProbabilityMeasure ℝ,
      (rdeOperator μ (ρ : Measure ℝ) = ρ ∧
        ∀ ρ' : ProbabilityMeasure ℝ, rdeOperator μ (ρ' : Measure ℝ) = ρ' → ρ' = ρ) ∧
      Integrable (posDiff κ) (μ.prod (ρ : Measure ℝ)) ∧
      Integrable (negDiff κ) (μ.prod (ρ : Measure ℝ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Ioi t)) atTop
        (𝓝 (kestenCplus κ μ ρ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Iio (-t))) atTop
        (𝓝 (kestenCminus κ μ ρ)) ∧
      (0 < kestenCplus κ μ ρ + kestenCminus κ μ ρ ↔
        ∀ c : ℝ, μ {p | p.1 = (1 - p.2) * c} < 1) := by sorry

end GoldieRenewal.Kesten

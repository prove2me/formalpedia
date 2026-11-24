-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_8_2
-- name    : GoldieRenewal.Implicit.Supplement.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:18:16.668829+00:00
-- url     : https://prove2.me/theorems/248feb27-4dd8-497e-8337-aca1b3d4b741
-- title:
--   Theorem 8.2 — S =_L MS + N√S + Q: t^κP(S > t) → C₊ of (8.4), positive iff P(Q > 0) + P(N > 0) > 0
-- statement:
--   Let $(Q,N,M)$ have joint law $\mu$ and $\kappa>0$. Suppose that $M$ satisfies the conditions of Lemma 2.2, that the conditions of Proposition 8.1 hold ($M\ge0$, $N\ge0$, $Q>0$ a.s. and (8.3)), with (8.2) strengthened to $EN^\kappa<\infty$, and that $EQ^\kappa<\infty$. Let $S$ have the law of Proposition 8.1, the unique law on $[0,\infty)$ satisfying (8.1), $S\overset{L}{=}MS+N\sqrt S+Q$ with $S$ independent of $(Q,N,M)$. Then $P(S>t)\sim C_+t^{-\kappa}$ as $t\to\infty$, where $m=E|M|^\kappa\log|M|$ and
--   $$
--   C_+=\frac1{\kappa m}E\bigl((MS+N\sqrt S+Q)^\kappa-(MS)^\kappa\bigr)\qquad(8.4).
--   $$
--   Also $C_+>0$ if and only if $P(Q>0)+P(N>0)>0$.
--
--   Since $S=R^2$ for the random polynomial equation (1.7), this gives the power-law tail of its solution.
--
--   **Formalization Note** Law-level statement: the conclusion first produces the law $\rho$ of $S$ (a probability law with no mass on $(-\infty,0)$, fixed by the law operator of (8.1), unique among such laws), then the integrability of the integrand of (8.4) against $\mu\otimes\rho$, the limit $t^\kappa\rho(t,\infty)\to C_+$ (p. 130 reading of $\sim$) and the positivity criterion. (8.3) is encoded as in Proposition 8.1. Moments are lower Lebesgue integrals. Under $Q>0$ a.s. the positivity criterion always holds; it is stated as printed.
--
--   Differences from the source:
--
--   - encoding: S is a random variable with the law of Proposition 8.1; P(S > t) ~ C₊t^{−κ} → a probability law ρ on [0, ∞) fixed by the law operator of (8.1), expectations against law(Q, N, M) ⊗ ρ; t^κρ(t, ∞) → C₊; reason: the paper's reading of ~ on p. 130; the law-level form of the published Theorem 4.1
--   - generalization: S is the solution of Proposition 8.1, and the expectation in (8.4) → the conclusion also asserts existence and uniqueness of the law of S on [0, ∞) and integrability of the integrand of (8.4); reason: existence and uniqueness follow from corrected Proposition 8.1: EQ^κ < ∞ with κ > 0 implies its additional E log⁺ Q < ∞ premise, and finiteness of (8.4) is proved on pp. 162–163; dropping these conjuncts gives the source statement
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 142, Theorem 8.2; proof pp. 162–163

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Theorem 8.2** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 142; random polynomial equation). Let `(Q, N, M)` have joint law
`μ`. Suppose `M` satisfies the conditions of Lemma 2.2 for `κ > 0`, that the conditions of
Proposition 8.1 hold (`M ≥ 0`, `N ≥ 0`, `Q > 0` a.s., (8.3)) with (8.2) strengthened to
`EN^κ < ∞`, and that `EQ^κ < ∞`. Then, for `S` with the law of Proposition 8.1 (the unique law on
`[0, ∞)` satisfying (8.1)), `P(S > t) ~ C₊ t^{−κ}` as `t → ∞`, where
(8.4) `C₊ = (κm)⁻¹ E((MS + N√S + Q)^κ − (MS)^κ)`. Also `C₊ > 0` iff `P(Q > 0) + P(N > 0) > 0`.

**Formalization Note** Law-level statement: `μ` is the law of `(Q, N, M)` (`p.1 = Q`, `p.2.1 = N`,
`p.2.2 = M`). The conclusion first identifies `S`: a law `ρ` on `[0, ∞)` fixed by `polyOperator μ`
and unique among such laws (Proposition 8.1, whose hypotheses are in force). Expectations involving
`S` are integrals against `μ ⊗ ρ`, so `S` is independent of `(Q, N, M)`; the conclusion also records
that the integrand of (8.4) is integrable (proved on pp. 162–163). (8.3) is encoded as in
Proposition 8.1 (`coeffLaw83`, `EReal`). "`P(S > t) ~ C₊t^{−κ}`" is `t^κ P(S > t) → C₊`
(p. 130). Moments are lower Lebesgue integrals. -/
theorem theorem_8_2 (κ : ℝ) (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map (fun p => p.2.2)))
    (hM_nonneg : μ {p | p.2.2 < 0} = 0) (hN_nonneg : μ {p | p.2.1 < 0} = 0)
    (hQ_pos : μ {p | p.1 ≤ 0} = 0)
    (hN : ∫⁻ p, ENNReal.ofReal (|p.2.1| ^ κ) ∂μ < ⊤)
    (h_8_3_plus : GoldieRenewal.Implicit.logPlusMoment (coeffLaw83 μ) < ⊤)
    (h_8_3 : GoldieRenewal.Implicit.logAbsMean (coeffLaw83 μ) < 0)
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ⊤) :
    ∃ ρ : ProbabilityMeasure ℝ,
      ((ρ : Measure ℝ) (Set.Iio 0) = 0 ∧ polyOperator μ (ρ : Measure ℝ) = ρ ∧
        ∀ ρ' : ProbabilityMeasure ℝ, (ρ' : Measure ℝ) (Set.Iio 0) = 0 →
          polyOperator μ (ρ' : Measure ℝ) = ρ' → ρ' = ρ) ∧
      Integrable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
          (p.1.2.2 * p.2 + p.1.2.1 * Real.sqrt p.2 + p.1.1) ^ κ - (p.1.2.2 * p.2) ^ κ)
        (μ.prod (ρ : Measure ℝ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Ioi t)) atTop
        (𝓝 ((κ * GoldieRenewal.Implicit.cramerMean κ (μ.map (fun p => p.2.2)))⁻¹ *
          ∫ p, ((p.1.2.2 * p.2 + p.1.2.1 * Real.sqrt p.2 + p.1.1) ^ κ - (p.1.2.2 * p.2) ^ κ)
            ∂(μ.prod (ρ : Measure ℝ)))) ∧
      (0 < (κ * GoldieRenewal.Implicit.cramerMean κ (μ.map (fun p => p.2.2)))⁻¹ *
          ∫ p, ((p.1.2.2 * p.2 + p.1.2.1 * Real.sqrt p.2 + p.1.1) ^ κ - (p.1.2.2 * p.2) ^ κ)
            ∂(μ.prod (ρ : Measure ℝ)) ↔
        0 < μ {p | 0 < p.1} + μ {p | 0 < p.2.1}) := by sorry

end GoldieRenewal.Implicit.Supplement

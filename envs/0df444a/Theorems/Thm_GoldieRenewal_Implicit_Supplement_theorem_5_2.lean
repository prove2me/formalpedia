-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_5_2
-- name    : GoldieRenewal.Implicit.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:15:43.636983+00:00
-- url     : https://prove2.me/theorems/ab9e54d3-9e57-438e-9c44-8833d02eab2a
-- title:
--   Theorem 5.2 — R =_L max(Q, MR): unique law, t^κP(R > t) → C₊ = (κm)⁻¹E((Q⁺ ∨ MR⁺)^κ − (MR⁺)^κ), C₊ > 0 iff P(Q > 0) > 0
-- statement:
--   Let $(Q,M)$ have joint law $\mu$, with $M\ge0$ a.s. Let $\kappa>0$, suppose $M$ satisfies the conditions of Lemma 2.2 ((2.3) $E|M|^\kappa=1$, (2.4) $E|M|^\kappa\log^+|M|<\infty$, (2.5) $\log|M|$ given $M\ne0$ nonarithmetic), and suppose $E(Q^+)^\kappa<\infty$. Write $m=E|M|^\kappa\log|M|$. Then there is a unique law for $R$ satisfying (1.2),
--   $$
--   R\overset{L}{=}\max(Q,MR),\qquad R\text{ independent of }(M,Q),
--   $$
--   and $P(R>t)\sim C_+t^{-\kappa}$ as $t\to\infty$, where
--   $$
--   C_+=\frac1{\kappa m}E\bigl((Q^+\vee MR^+)^\kappa-(MR^+)^\kappa\bigr).
--   $$
--   Also $C_+>0$ if and only if $P(Q>0)>0$.
--
--   With $Q=1$ or $M=e^{B-A}$, $Q=e^B$, $\log R$ is the overall maximum of a random walk or the stationary queueing time of a G/G/1 queue, so this recovers the exponential decay of those upper tails.
--
--   **Formalization Note** The statement is at the level of laws, as in the published Theorem 4.1: a law for $R$ satisfying (1.2) is a probability measure fixed by the law operator of (1.2), unique among all probability laws, and expectations involving $R$ are integrals against law$(Q,M)\otimes$law$(R)$. $P(R>t)\sim C_+t^{-\kappa}$ means $t^\kappa P(R>t)\to C_+$, which covers $C_+=0$ (p. 130). The conclusion also states that the integrand of $C_+$ is integrable, so that the expectation is a genuine one.
--
--   Differences from the source:
--
--   - encoding: R is a random variable with R =_L max(Q, MR), R independent of (M, Q); P(R > t) ~ C₊t^{−κ} → a probability law ρ fixed by the law operator of (1.2), expectations against law(Q, M) ⊗ ρ; t^κρ(t, ∞) → C₊; reason: the paper's reading of ~ on p. 130 includes C₊ = 0; the law-level form is that of the published Theorem 4.1
--   - generalization: the expectation defining C₊ → the conclusion also asserts that (Q⁺ ∨ MR⁺)^κ − (MR⁺)^κ is integrable; reason: the proof shows E|(Q ∨ MR)⁺)^κ − ((MR)⁺)^κ| ≤ E(Q⁺)^κ (p. 159); the added conjunct makes the Bochner integral the paper's expectation, and dropping it gives the source statement
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 139, Theorem 5.2; proof p. 159

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Theorem 5.2** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 139; random extremal equation). Let `(Q, M)` have joint law `μ`,
with `M ≥ 0` a.s., `M` satisfying the conditions of Lemma 2.2 for `κ > 0`, and `E(Q⁺)^κ < ∞`. Then
there is a unique law for `R` satisfying (1.2) `R =_L max(Q, MR)`, `R` independent of `(M, Q)`, and
for it `P(R > t) ~ C₊ t^{−κ}` as `t → ∞`, where
`C₊ = (κm)⁻¹ E((Q⁺ ∨ MR⁺)^κ − (MR⁺)^κ)`, `m = E|M|^κ log|M|`. Also `C₊ > 0` iff `P(Q > 0) > 0`.

**Formalization Note** Law-level statement, as in the published `GoldieRenewal.Kesten.theorem_4_1`:
`μ` is the law of `(Q, M)` (first coordinate `Q`); a law for `R` satisfying (1.2) is a probability
measure `ρ` with `extremalOperator μ ρ = ρ`, unique among all probability laws on `ℝ`; expectations
involving `R` are integrals against `μ ⊗ ρ` (`R` independent of `(Q, M)`). `Q⁺ ∨ MR⁺` is
`max(Q⁺, M R⁺)` (§1: `∨` binds less tightly than `·`). "`P(R > t) ~ C₊t^{−κ}`" is
`t^κ P(R > t) → C₊` (p. 130; covers `C₊ = 0`). The conclusion also records that the integrand of
`C₊` is integrable (proved on p. 159), so the Bochner integral is the paper's expectation.
`E(Q⁺)^κ` is a lower Lebesgue integral. -/
theorem theorem_5_2 (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM_nonneg : μ {p | p.2 < 0} = 0)
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (max p.1 0 ^ κ) ∂μ < ⊤) :
    ∃ ρ : ProbabilityMeasure ℝ,
      (extremalOperator μ (ρ : Measure ℝ) = ρ ∧
        ∀ ρ' : ProbabilityMeasure ℝ, extremalOperator μ (ρ' : Measure ℝ) = ρ' → ρ' = ρ) ∧
      Integrable (fun p : (ℝ × ℝ) × ℝ =>
          max (max p.1.1 0) (p.1.2 * max p.2 0) ^ κ - (p.1.2 * max p.2 0) ^ κ)
        (μ.prod (ρ : Measure ℝ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Ioi t)) atTop
        (𝓝 ((κ * GoldieRenewal.Implicit.cramerMean κ (μ.map Prod.snd))⁻¹ *
          ∫ p, (max (max p.1.1 0) (p.1.2 * max p.2 0) ^ κ - (p.1.2 * max p.2 0) ^ κ)
            ∂(μ.prod (ρ : Measure ℝ)))) ∧
      (0 < (κ * GoldieRenewal.Implicit.cramerMean κ (μ.map Prod.snd))⁻¹ *
          ∫ p, (max (max p.1.1 0) (p.1.2 * max p.2 0) ^ κ - (p.1.2 * max p.2 0) ^ κ)
            ∂(μ.prod (ρ : Measure ℝ)) ↔
        0 < μ {p | 0 < p.1}) := by sorry

end GoldieRenewal.Implicit.Supplement

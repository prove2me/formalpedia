-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_6_2
-- name    : GoldieRenewal.Implicit.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:16:45.055238+00:00
-- url     : https://prove2.me/theorems/55792af6-ad24-43f4-8737-49faa6a6b32b
-- title:
--   Theorem 6.2 — R =_L Q + M max(L, R): unique law, t^κP(R > t) → C₊ of the stated formula, and a sufficient condition for C₊ > 0
-- statement:
--   Let $(Q,M,L)$ have joint law $\mu$, with $M\ge0$ a.s. Let $\kappa>0$, suppose $M$ satisfies the conditions of Lemma 2.2, and
--   $$
--   E(ML^+)^\kappa<\infty,\qquad E|Q|^\kappa<\infty\qquad(6.3).
--   $$
--   Write $m=E|M|^\kappa\log|M|$. Then there is a unique law for $R$ satisfying (1.3), $R\overset{L}{=}Q+M\max(L,R)$ with $R$ independent of $(L,M,Q)$, and $P(R>t)\sim C_+t^{-\kappa}$ as $t\to\infty$, where
--   $$
--   C_+=\frac1{\kappa m}E\Bigl(\bigl((Q+M\max(L,R))^+\bigr)^\kappa-\bigl((MR)^+\bigr)^\kappa\Bigr).
--   $$
--   If, further, there is a constant $c$ such that $Q-c(1-M)\ge0$ a.s. and
--   $$
--   P(Q-c(1-M)>0)+P(M(L-c)>0)>0,
--   $$
--   then $C_+>0$.
--
--   Equation (1.3) is Model E of Letac (1986); with $Q=0$ and $L>0$ it describes $S=\log R$ satisfying $S\overset{L}{=}B+A\vee S$.
--
--   **Formalization Note** Law-level statement, as in the published Theorem 4.1: $\mu$ is the law of $(Q,M,L)$; a law satisfying (1.3) is a probability measure fixed by the law operator of (1.3), unique among all probability laws; expectations involving $R$ are integrals against $\mu\otimes$law$(R)$. $P(R>t)\sim C_+t^{-\kappa}$ means $t^\kappa P(R>t)\to C_+$. The conclusion also states that the integrand of $C_+$ is integrable. The positivity clause is the one-way implication of the paper, for every $c$.
--
--   Differences from the source:
--
--   - encoding: R is a random variable solving (1.3); P(R > t) ~ C₊t^{−κ} → a probability law ρ fixed by the law operator of (1.3), expectations against law(Q, M, L) ⊗ ρ; t^κρ(t, ∞) → C₊; reason: the paper's reading of ~ on p. 130; the law-level form of the published Theorem 4.1
--   - encoding: if there is a constant c such that …, then C₊ > 0 → for every c, if … then C₊ > 0; reason: logically the same statement
--   - generalization: the expectation defining C₊ → the conclusion also asserts that ((Q + M max(L, R))⁺)^κ − ((MR)⁺)^κ is integrable; reason: this is (2.16), verified in the proof (pp. 159–160); dropping the conjunct gives the source statement
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 140, Theorem 6.2; proof pp. 159–161

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Theorem 6.2** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 140; Letac's model E). Let `(Q, M, L)` have joint law `μ`, with
`M ≥ 0` a.s., `M` satisfying the conditions of Lemma 2.2 for `κ > 0`, and (6.3) `E(ML⁺)^κ < ∞`,
`E|Q|^κ < ∞`. Then there is a unique law for `R` satisfying (1.3) `R =_L Q + M max(L, R)`, `R`
independent of `(L, M, Q)`, and for it `P(R > t) ~ C₊ t^{−κ}` as `t → ∞`, where
`C₊ = (κm)⁻¹ E(((Q + M max(L, R))⁺)^κ − ((MR)⁺)^κ)`. If, further, there is a constant `c` with
`Q − c(1 − M) ≥ 0` a.s. and `P(Q − c(1 − M) > 0) + P(M(L − c) > 0) > 0`, then `C₊ > 0`.

**Formalization Note** Law-level statement: `μ` is the law of `(Q, M, L)` (`p.1 = Q`, `p.2.1 = M`,
`p.2.2 = L`); a law for `R` satisfying (1.3) is a probability measure fixed by `letacEOperator μ`,
unique among all probability laws on `ℝ`; expectations involving `R` are integrals against `μ ⊗ ρ`.
"`P(R > t) ~ C₊t^{−κ}`" is `t^κ P(R > t) → C₊` (p. 130). The conclusion also records that the
integrand of `C₊` is integrable (the paper verifies (2.16), pp. 159–160). Moments are lower
Lebesgue integrals. The positivity clause is a one-way implication, quantified over `c`. -/
theorem theorem_6_2 (κ : ℝ) (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM_nonneg : μ {p | p.2.1 < 0} = 0)
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map (fun p => p.2.1)))
    (hML : ∫⁻ p, ENNReal.ofReal ((p.2.1 * max p.2.2 0) ^ κ) ∂μ < ⊤)
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ⊤) :
    ∃ ρ : ProbabilityMeasure ℝ,
      (letacEOperator μ (ρ : Measure ℝ) = ρ ∧
        ∀ ρ' : ProbabilityMeasure ℝ, letacEOperator μ (ρ' : Measure ℝ) = ρ' → ρ' = ρ) ∧
      Integrable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
          max (p.1.1 + p.1.2.1 * max p.1.2.2 p.2) 0 ^ κ - max (p.1.2.1 * p.2) 0 ^ κ)
        (μ.prod (ρ : Measure ℝ)) ∧
      Tendsto (fun t : ℝ => t ^ κ * (ρ : Measure ℝ).real (Set.Ioi t)) atTop
        (𝓝 ((κ * GoldieRenewal.Implicit.cramerMean κ (μ.map (fun p => p.2.1)))⁻¹ *
          ∫ p, (max (p.1.1 + p.1.2.1 * max p.1.2.2 p.2) 0 ^ κ - max (p.1.2.1 * p.2) 0 ^ κ)
            ∂(μ.prod (ρ : Measure ℝ)))) ∧
      (∀ c : ℝ, μ {p | p.1 - c * (1 - p.2.1) < 0} = 0 →
        0 < μ {p | 0 < p.1 - c * (1 - p.2.1)} + μ {p | 0 < p.2.1 * (p.2.2 - c)} →
        0 < (κ * GoldieRenewal.Implicit.cramerMean κ (μ.map (fun p => p.2.1)))⁻¹ *
          ∫ p, (max (p.1.1 + p.1.2.1 * max p.1.2.2 p.2) 0 ^ κ - max (p.1.2.1 * p.2) 0 ^ κ)
            ∂(μ.prod (ρ : Measure ℝ))) := by sorry

end GoldieRenewal.Implicit.Supplement

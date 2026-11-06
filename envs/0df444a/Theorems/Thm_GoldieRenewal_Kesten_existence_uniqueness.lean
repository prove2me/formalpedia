-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_existence_uniqueness
-- name    : GoldieRenewal.Kesten.existence_uniqueness
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T04:15:18.218187+00:00
-- url     : https://prove2.me/theorems/9495414e-b4e8-4e0e-83e6-f4e72376a2c2
-- title:
--   Theorem 4.1 (part 1) — R =_L Q + MR has a unique stationary law
-- statement:
--   Let $Q$ and $M$ be random variables with joint law $\mu$ on $\mathbb R^2$ (no independence and no sign condition is assumed). Suppose $M$ satisfies the conditions of Lemma 2.2 for some $\kappa>0$: $\mathbf E|M|^\kappa=1$, $\mathbf E|M|^\kappa\log^+|M|<\infty$, and the conditional law of $\log|M|$ given $M\ne0$ is nonarithmetic. Suppose also that (4.2) $\mathbf E|Q|^\kappa<\infty$.
--
--   Then there is a **unique** probability law $\rho$ on $\mathbb R$ for $R$ satisfying the random difference equation
--   $$R\overset{\mathcal L}{=}Q+MR,\qquad R\text{ independent of }(Q,M)\qquad(1.1).$$
--   That is, $\rho$ is the law of $Q+MR$ when $((Q,M),R)\sim\mu\otimes\rho$, and every probability law with this property equals $\rho$.
--
--   This is the first assertion of Theorem 4.1 (Kesten's theorem in dimension one). It is the classical existence and uniqueness of the stationary law of the affine recursion $R_n=Q_n+M_nR_{n-1}$. Under the hypotheses, Lemma 2.2 gives $\mathbf E\log|M|<0$, and $\mathbf E|Q|^\kappa<\infty$ gives $\mathbf E\log^+|Q|<\infty$. The stationary law is then the law of the a.s. convergent perpetuity $\sum_{k\ge1}\Pi_{k-1}Q_k$.
--
--   **Formalization Note** A law for $R$ satisfying (1.1) is a probability measure $\rho$ with `rdeOperator μ ρ = ρ`, i.e. the image of $\mu\otimes\rho$ under $((q,m),r)\mapsto q+mr$ equals $\rho$. Uniqueness is among all probability laws on $\mathbb R$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 135, Theorem 4.1 (first assertion: 'there is a unique law for R satisfying (1.1)'); classical, cf. Kesten (1973), Vervaat (1979)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 4.1, part 1: existence and uniqueness of the law of `R`** (Goldie, *Implicit renewal
theory and tails of solutions of random equations*, Ann. Appl. Probab. 1(1) (1991), p. 135,
Theorem 4.1: "there is a unique law for `R` satisfying (1.1)"). Let `(Q, M)` have joint law `μ`,
let `M` satisfy the conditions of Lemma 2.2 for some `κ > 0`, and suppose (4.2) `E|Q|^κ < ∞`.
Then there is exactly one probability law `ρ` on `ℝ` with `R =_L Q + MR`, `R` independent of
`(Q, M)`.

**Formalization Note** A law for `R` satisfying (1.1) is a probability measure `ρ` with
`rdeOperator μ ρ = ρ`; uniqueness is among all probability laws on `ℝ`. This is the first
conjunct of `GoldieRenewal.Kesten.theorem_4_1`. -/
theorem existence_uniqueness (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞) :
    ∃ ρ : ProbabilityMeasure ℝ,
      rdeOperator μ (ρ : Measure ℝ) = ρ ∧
        ∀ ρ' : ProbabilityMeasure ℝ, rdeOperator μ (ρ' : Measure ℝ) = ρ' → ρ' = ρ := by sorry

end GoldieRenewal.Kesten

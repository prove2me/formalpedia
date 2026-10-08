-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_integrability_2_16_2_17
-- name    : GoldieRenewal.Kesten.integrability_2_16_2_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:10.131115+00:00
-- url     : https://prove2.me/theorems/a32fc1f1-5366-443e-b7fc-1a2d5ed6cc78
-- title:
--   Proof of Theorem 4.1, pp. 156–157 — (2.16) and (2.17) hold for Ψ(t) = Q + Mt
-- statement:
--   Let $(Q,M)$ have joint law $\mu$, let $M$ satisfy the conditions of Lemma 2.2 for some $\kappa>0$, and suppose $\mathbf E|Q|^\kappa<\infty$ (4.2). Let $R$ have a law $\rho$ satisfying $R\overset{\mathcal L}{=}Q+MR$, and take $R$ independent of $(Q,M)$. Then
--
--   $$
--   \mathbf E\big|((Q+MR)^+)^\kappa-((MR)^+)^\kappa\big|<\infty
--   \quad\text{and}\quad
--   \mathbf E\big|((Q+MR)^-)^\kappa-((MR)^-)^\kappa\big|<\infty .
--   $$
--
--   These are conditions (2.16) and (2.17) of Corollary 2.4 for the random function $\Psi(t)=Q+Mt$; with them Corollary 2.4 yields the tail asymptotics of Theorem 4.1. Note that $\mathbf E|R|^\kappa$ is typically infinite, so the two differences must be handled jointly rather than term by term.
--
--   **Formalization Note** The pair $((Q,M),R)$ has law $\mu\otimes\rho$. The statement is made for every law solving the equation; by Theorem 4.1 there is exactly one.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, pp. 156–157, proof of Theorem 4.1 (I₁–I₄), unnumbered

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **(2.16) and (2.17) for `Ψ(t) = Q + Mt`** (Goldie, *Implicit renewal theory and tails of
solutions of random equations*, Ann. Appl. Probab. 1(1) (1991), pp. 156–157, proof of
Theorem 4.1, unnumbered: "Thus (2.16) is proved, and (2.17) follows similarly"). Under the
hypotheses of Theorem 4.1 (`M` satisfies the conditions of Lemma 2.2, (4.2) `E|Q|^κ < ∞`), let
`ρ` be a law for `R` satisfying (1.1). With `R` of law `ρ` independent of `(Q, M)`,
`E|((Q + MR)⁺)^κ − ((MR)⁺)^κ| < ∞` and `E|((Q + MR)⁻)^κ − ((MR)⁻)^κ| < ∞`.

**Formalization Note** The pair `((Q, M), R)` has law `μ ⊗ ρ`; finiteness of `E|·|` is
`Integrable`. The statement is for every probability law `ρ` solving (1.1) (by Theorem 4.1 there
is exactly one). -/
theorem integrability_2_16_2_17 (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞)
    (ρ : ProbabilityMeasure ℝ) (hρ : rdeOperator μ (ρ : Measure ℝ) = ρ) :
    Integrable (posDiff κ) (μ.prod (ρ : Measure ℝ)) ∧
      Integrable (negDiff κ) (μ.prod (ρ : Measure ℝ)) := by sorry

end GoldieRenewal.Kesten

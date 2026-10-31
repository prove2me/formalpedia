-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_7_7
-- name    : KallMayerSLP.RiskMeasures.proposition_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:41.408302+00:00
-- url     : https://prove2.me/theorems/9bee01d6-ddf1-47ab-82f5-a6c9a1968c06
-- title:
--   Proposition 7.7 — $\rho^\pm_{\mathrm{jic}}$ are positive homogeneous, subadditive and monotone
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $s\ge1$. For $s$-dimensional random vectors $\vartheta=(\vartheta_1,\dots,\vartheta_s)$ with integrable components, let
--   $$
--   \rho^+_{\mathrm{jic}}(\vartheta):=\mathbb E\Big[\max_{1\le i\le s}\vartheta_i^+\Big],\qquad
--   \rho^-_{\mathrm{jic}}(\vartheta):=\mathbb E\Big[\max_{1\le i\le s}\vartheta_i^-\Big].
--   $$
--   Both are positive homogeneous and subadditive. Moreover $\rho^+_{\mathrm{jic}}$ is monotonically increasing and $\rho^-_{\mathrm{jic}}$ is monotonically decreasing with respect to the componentwise order.
--
--   These are the risk measures of joint integrated chance constraints (§4.1); by Proposition 7.1 they are convex.
--
--   **Formalization Note** The random vectors form $\mathcal L^1_s$ (`Lspace (Fin s → ℝ) 1 P`), with components indexed from $0$. The order hypothesis $\vartheta_1\le\vartheta_2$ is componentwise and almost sure. The statement is made for every $s\in\mathbb N$; at $s=0$ both functionals vanish.
--
--   Differences from the source:
--   - reading: ϑ ∈ 𝓛¹₁ for the s-dimensional random vector ϑ (as printed in (P)) → ϑ ∈ 𝓛¹_s (Lspace (Fin s → ℝ) 1 P); reason: the printed subscript 1 is the dimension of a scalar variable; ϑ is s-dimensional, so the space is 𝓛¹_s of (1.6)
--   - reading: "monotonous" → ρ⁺_jic increasing, ρ⁻_jic decreasing, in the componentwise order; reason: the directions stated in the book's proof, p.189
--   - generalization: ϑ₁ ≤ ϑ₂ componentwise (pointwise) → ϑ₁ ≤ ϑ₂ almost surely; reason: a weaker hypothesis than the pointwise order of the book's proof ("ϑ₁(ω) ≤ ϑ₂(ω) for all ω"), so the monotonicity clause implies the book's
--   - encoding: 1 ≤ i ≤ s, s ≥ 1 implicit → i : Fin s (index base 0), any s ∈ ℕ; reason: at s = 0 both functionals are 0 and every clause holds trivially; for s ≥ 1 the same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, (P), p.188 (PDF 198), and Proposition 7.7 with its proof, p.189 (PDF 199)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_Lspace
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoJicPlus
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoJicMinus

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 7.7** (joint integrated-chance-constraint risk measures).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, (P) p.188 (PDF 198) and Prop. 7.7, p.189 (PDF 199), with the directions of
monotonicity from its proof. For an `s`-dimensional random vector `ϑ ∈ 𝓛¹_s`, both
`ρ⁺_jic(ϑ) := 𝔼[max_{1≤i≤s} ϑ_i⁺]` and `ρ⁻_jic(ϑ) := 𝔼[max_{1≤i≤s} ϑ_i⁻]` are positive
homogeneous and subadditive; moreover `ρ⁺_jic` is monotonically increasing and `ρ⁻_jic` is
monotonically decreasing.

**Formalization Note.** `𝓛¹_s` is `Lspace (Fin s → ℝ) 1 P` (integrable random vectors, index
base 0). The order on random vectors is componentwise, almost surely (`ϑ₁ ω i ≤ ϑ₂ ω i` for all `i`,
for `P`-almost every `ω`), weaker than pointwise, so the statement is stronger. Any `s` is allowed; for `s = 0` both functionals are `0`. -/
theorem proposition_7_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ) :
    (IsPosHomogeneous (fun ϑ : Lspace (Fin s → ℝ) 1 P => rhoJicPlus P (ϑ : Ω → Fin s → ℝ)) ∧
      IsSubadditive (fun ϑ : Lspace (Fin s → ℝ) 1 P => rhoJicPlus P (ϑ : Ω → Fin s → ℝ)) ∧
      ∀ ϑ₁ ∈ Lspace (Fin s → ℝ) 1 P, ∀ ϑ₂ ∈ Lspace (Fin s → ℝ) 1 P, ϑ₁ ≤ᵐ[P] ϑ₂ →
        rhoJicPlus P ϑ₁ ≤ rhoJicPlus P ϑ₂) ∧
    (IsPosHomogeneous (fun ϑ : Lspace (Fin s → ℝ) 1 P => rhoJicMinus P (ϑ : Ω → Fin s → ℝ)) ∧
      IsSubadditive (fun ϑ : Lspace (Fin s → ℝ) 1 P => rhoJicMinus P (ϑ : Ω → Fin s → ℝ)) ∧
      ∀ ϑ₁ ∈ Lspace (Fin s → ℝ) 1 P, ∀ ϑ₂ ∈ Lspace (Fin s → ℝ) 1 P, ϑ₁ ≤ᵐ[P] ϑ₂ →
        rhoJicMinus P ϑ₂ ≤ rhoJicMinus P ϑ₁) := by sorry

end KallMayerSLP.RiskMeasures

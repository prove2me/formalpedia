-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_7_4
-- name    : KallMayerSLP.RiskMeasures.proposition_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:07.89799+00:00
-- url     : https://prove2.me/theorems/e0c42cc6-8280-4f20-9cf2-df7516b1963d
-- title:
--   Proposition 7.4 — $\rho^\pm_{\mathrm{sic}}$ and $\rho^\alpha_{\mathrm{sic}}$ are positive homogeneous, subadditive and monotone
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. On $\mathcal L^1_1$ the following risk measures are positive homogeneous and subadditive, and monotone:
--
--   1. (D1) $\rho^+_{\mathrm{sic}}(\vartheta):=\mathbb E[\vartheta^+]$ is monotonically increasing;
--   2. (D2) $\rho^-_{\mathrm{sic}}(\vartheta):=\mathbb E[\vartheta^-]$ is monotonically decreasing;
--   3. (E) for every $0\le\alpha\le\tfrac12$, $\rho^\alpha_{\mathrm{sic}}(\vartheta):=\alpha\,\mathbb E[\vartheta]+(1-2\alpha)\,\mathbb E[\vartheta^+]$ is monotonically increasing.
--
--   They are therefore convex (Proposition 7.1), although translation invariance fails.
--
--   **Formalization Note** The direction of monotonicity of each measure is the one established in the book's proof. The monotonicity hypothesis $\vartheta_1\le\vartheta_2$ is almost sure.
--
--   Differences from the source:
--   - reading: "monotonous" → ρ⁺_sic and ρ^α_sic increasing, ρ⁻_sic decreasing; reason: the directions stated in the book's proof, pp.186–187
--   - generalization: ϑ₁ ≤ ϑ₂ (pointwise) → ϑ₁ ≤ ϑ₂ almost surely; reason: a weaker hypothesis than the pointwise order of the book's proof ("ϑ₁(ω) ≤ ϑ₂(ω) for all ω"), so the monotonicity clause implies the book's
--   - encoding: 𝓛^p₁ (p = 1, 2, ∞) of (1.6) → Lspace ℝ p P: functions Ω → ℝ with MemLp · p P, a submodule of Ω → ℝ; reason: random variables with finite p-th moment (resp. bounded support); same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.4, p.186 (PDF 196), with its proof, pp.186–187 (PDF 196–197)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_Lspace
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoSicPlus
import Definitions.Def_KallMayerSLP_CondExp_rhoSicMinus
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoSicAlpha

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 7.4** (separate integrated-chance-constraint risk measures).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.4, p.186 (PDF 196), with the directions of monotonicity from its proof
(pp.186–187, PDF 196–197). The following risk measures on `𝓛¹₁` are positive homogeneous and
subadditive, and monotonous:
(D1) `ρ⁺_sic(ϑ) := 𝔼[ϑ⁺]`, monotonically increasing;
(D2) `ρ⁻_sic(ϑ) := 𝔼[ϑ⁻]`, monotonically decreasing;
(E) `ρ^α_sic(ϑ) := α𝔼[ϑ] + (1 − 2α)𝔼[ϑ⁺]`, `0 ≤ α ≤ 1/2`, monotonically increasing.

**Formalization Note.** `𝓛¹₁` is `Lspace ℝ 1 P`; positive homogeneity and subadditivity are
those of the restriction to `𝓛¹₁`. The hypothesis of monotonicity is `ϑ₁ ≤ ϑ₂` almost surely
(weaker than pointwise, so the statement is stronger). -/
theorem proposition_7_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    (IsPosHomogeneous (fun ϑ : Lspace ℝ 1 P => rhoSicPlus P ϑ) ∧
      IsSubadditive (fun ϑ : Lspace ℝ 1 P => rhoSicPlus P ϑ) ∧
      ∀ ϑ₁ ∈ Lspace ℝ 1 P, ∀ ϑ₂ ∈ Lspace ℝ 1 P, ϑ₁ ≤ᵐ[P] ϑ₂ → rhoSicPlus P ϑ₁ ≤ rhoSicPlus P ϑ₂) ∧
    (IsPosHomogeneous (fun ϑ : Lspace ℝ 1 P => KallMayerSLP.CondExp.rhoSicMinus P ϑ) ∧
      IsSubadditive (fun ϑ : Lspace ℝ 1 P => KallMayerSLP.CondExp.rhoSicMinus P ϑ) ∧
      ∀ ϑ₁ ∈ Lspace ℝ 1 P, ∀ ϑ₂ ∈ Lspace ℝ 1 P, ϑ₁ ≤ᵐ[P] ϑ₂ → KallMayerSLP.CondExp.rhoSicMinus P ϑ₂ ≤ KallMayerSLP.CondExp.rhoSicMinus P ϑ₁) ∧
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 / 2 →
      IsPosHomogeneous (fun ϑ : Lspace ℝ 1 P => rhoSicAlpha P α ϑ) ∧
      IsSubadditive (fun ϑ : Lspace ℝ 1 P => rhoSicAlpha P α ϑ) ∧
      ∀ ϑ₁ ∈ Lspace ℝ 1 P, ∀ ϑ₂ ∈ Lspace ℝ 1 P, ϑ₁ ≤ᵐ[P] ϑ₂ →
        rhoSicAlpha P α ϑ₁ ≤ rhoSicAlpha P α ϑ₂) := by sorry

end KallMayerSLP.RiskMeasures

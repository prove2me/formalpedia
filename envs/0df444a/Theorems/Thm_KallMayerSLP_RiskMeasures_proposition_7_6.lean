-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_7_6
-- name    : KallMayerSLP.RiskMeasures.proposition_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:11.726997+00:00
-- url     : https://prove2.me/theorems/9a0b8bff-e542-4b9a-89e2-fba443632dc7
-- title:
--   Proposition 7.6 — standard deviation, MAD and their one-sided versions are deviation measures
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. The following functionals are deviation measures in the sense of the axioms (7.4):
--
--   1. (I) $\rho_{\mathrm{Std}}(\vartheta):=\sigma(\vartheta):=\sqrt{\mathbb E[(\vartheta-\mathbb E[\vartheta])^2]}$ on $\mathcal L^2_1$;
--   2. (J) $\rho_{\mathrm{MAD}}(\vartheta):=\mathbb E\big[|\vartheta-\mathbb E[\vartheta]|\big]$ on $\mathcal L^1_1$;
--   3. (K) $\rho^+_{\mathrm{Std}}(\vartheta):=\sqrt{\mathbb E[((\vartheta-\mathbb E[\vartheta])^+)^2]}$ and $\rho^-_{\mathrm{Std}}(\vartheta):=\sqrt{\mathbb E[((\vartheta-\mathbb E[\vartheta])^-)^2]}$ on $\mathcal L^1_1$;
--   4. (L) $\rho^+_{\mathrm{MAD}}(\vartheta):=\mathbb E[(\vartheta-\mathbb E[\vartheta])^+]$ and $\rho^-_{\mathrm{MAD}}(\vartheta):=\mathbb E[(\vartheta-\mathbb E[\vartheta])^-]$ on $\mathcal L^1_1$, and moreover
--   $$
--   \rho^+_{\mathrm{MAD}}(\vartheta)=\rho^-_{\mathrm{MAD}}(\vartheta)=\tfrac12\,\rho_{\mathrm{MAD}}(\vartheta)\qquad(\vartheta\in\mathcal L^1_1).
--   $$
--
--   That is, each is subadditive, positive homogeneous, strictly positive on non-constant random variables and zero on constants, and invariant under adding a constant.
--
--   **Formalization Note** "Constant" means almost surely constant. On $\mathcal L^1_1$ the semideviations in (K) may be $+\infty$, so (K) is stated for functionals with values in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: "ϑ non-constant" / "constant" in (D3) → not almost surely constant / almost surely constant; reason: every functional listed is an expectation and cannot see null sets; under the pointwise reading (D3) fails for each of them
--   - reading: σ⁺ and σ⁻ of (K) on 𝓛¹₁, as real-valued functions (p.182: "ρ : Υ → ℝ a real–valued function") → σ⁺ and σ⁻ of (K) with values in [0, ∞] on 𝓛¹₁; homogeneity ρ(λϑ) = λρ(ϑ) with λ ≥ 0 cast to [0, ∞]; subadditivity in [0, ∞]; reason: on 𝓛¹₁ the second moment can be infinite (density 2t⁻³ on [1, ∞)), so the printed real-valued reading is ill-posed; the extended-valued reading keeps the printed domain and contains the real-valued statement on 𝓛²₁ (paper.md, reading 2), where the values are finite
--   - encoding: 𝓛^p₁ (p = 1, 2, ∞) of (1.6) → Lspace ℝ p P: functions Ω → ℝ with MemLp · p P, a submodule of Ω → ℝ; reason: random variables with finite p-th moment (resp. bounded support); same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.6, p.188 (PDF 198); axioms (7.4), p.183 (PDF 193)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_Lspace
import Definitions.Def_KallMayerSLP_RiskMeasures_IsDeviationMeasure
import Definitions.Def_KallMayerSLP_RiskMeasures_IsDeviationMeasureENN
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoStd
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoMAD
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoStdPlus
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoStdMinus
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoMADPlus
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoMADMinus

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 7.6** (deviation measures).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.6, p.188 (PDF 198). The following risk measures are deviation measures
according to the axioms (7.4):
(I) `ρ_Std(ϑ) := σ(ϑ) := √(𝔼[(ϑ − 𝔼[ϑ])²])`, `ϑ ∈ 𝓛²₁`;
(J) `ρ_MAD(ϑ) := 𝔼[|ϑ − 𝔼[ϑ]|]`, `ϑ ∈ 𝓛¹₁`;
(K) `ρ⁺_Std(ϑ) := √(𝔼[((ϑ − 𝔼[ϑ])⁺)²])` and `ρ⁻_Std(ϑ) := √(𝔼[((ϑ − 𝔼[ϑ])⁻)²])`, `ϑ ∈ 𝓛¹₁`;
(L) `ρ⁺_MAD(ϑ) := 𝔼[(ϑ − 𝔼[ϑ])⁺] = ½ρ_MAD(ϑ)` and `ρ⁻_MAD(ϑ) := 𝔼[(ϑ − 𝔼[ϑ])⁻] = ½ρ_MAD(ϑ)`,
`ϑ ∈ 𝓛¹₁`.

**Formalization Note.** `𝓛^p₁` is `Lspace ℝ p P`. "Constant" in (7.4) is "almost surely
constant". On the printed domain `𝓛¹₁` of (K) the semideviations can be `+∞`, so (K) is stated
with values in `[0, ∞]` (`IsDeviationMeasureENN`); on `𝓛²₁` they are finite. The identities
printed in (L) are part of the statement. -/
theorem proposition_7_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    IsDeviationMeasure P (Lspace ℝ 2 P) (rhoStd P) ∧
    IsDeviationMeasure P (Lspace ℝ 1 P) (rhoMAD P) ∧
    (IsDeviationMeasureENN P (Lspace ℝ 1 P) (rhoStdPlus P) ∧
      IsDeviationMeasureENN P (Lspace ℝ 1 P) (rhoStdMinus P)) ∧
    (IsDeviationMeasure P (Lspace ℝ 1 P) (rhoMADPlus P) ∧
      IsDeviationMeasure P (Lspace ℝ 1 P) (rhoMADMinus P) ∧
      ∀ ϑ ∈ Lspace ℝ 1 P, rhoMADPlus P ϑ = rhoMAD P ϑ / 2 ∧ rhoMADMinus P ϑ = rhoMAD P ϑ / 2) := by sorry

end KallMayerSLP.RiskMeasures

-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_7_5
-- name    : KallMayerSLP.RiskMeasures.proposition_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:22.428601+00:00
-- url     : https://prove2.me/theorems/500a9d58-9c3d-40f0-bf5c-c774438e5041
-- title:
--   Proposition 7.5 — $\rho_Q$, $\rho_A$ and $\rho^\pm_Q$ are positive homogeneous and subadditive
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. The following risk measures are positive homogeneous and subadditive:
--
--   1. (F) $\rho_Q(\vartheta):=\sqrt{\mathbb E[\vartheta^2]}$ on $\mathcal L^2_1$;
--   2. (G) $\rho_A(\vartheta):=\mathbb E[|\vartheta|]$ on $\mathcal L^1_1$;
--   3. (H) $\rho^+_Q(\vartheta):=\sqrt{\mathbb E[(\vartheta^+)^2]}$ and $\rho^-_Q(\vartheta):=\sqrt{\mathbb E[(\vartheta^-)^2]}$ on $\mathcal L^1_1$.
--
--   By Proposition 7.1 they are convex; neither monotonicity nor translation invariance holds for them.
--
--   **Formalization Note** On $\mathcal L^1_1$ the second moments in (H) may be infinite, so $\rho^\pm_Q$ are taken with values in $[0,\infty]$: positive homogeneity reads $\rho(\lambda\vartheta)=\lambda\rho(\vartheta)$ for real $\lambda\ge0$ (with $0\cdot\infty=0$) and subadditivity is an inequality in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: ρ⁺_Q and ρ⁻_Q of (H) on 𝓛¹₁, as real-valued functions (p.182: "ρ : Υ → ℝ a real–valued function") → ρ⁺_Q and ρ⁻_Q of (H) with values in [0, ∞] on 𝓛¹₁; homogeneity ρ(λϑ) = λρ(ϑ) with λ ≥ 0 cast to [0, ∞]; subadditivity in [0, ∞]; reason: on 𝓛¹₁ the second moment can be infinite (density 2t⁻³ on [1, ∞)), so the printed real-valued reading is ill-posed; the extended-valued reading keeps the printed domain and contains the real-valued statement on 𝓛²₁ (paper.md, reading 2), where the values are finite
--   - encoding: 𝓛^p₁ (p = 1, 2, ∞) of (1.6) → Lspace ℝ p P: functions Ω → ℝ with MemLp · p P, a submodule of Ω → ℝ; reason: random variables with finite p-th moment (resp. bounded support); same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.5, p.187 (PDF 197)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_Lspace
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoQ
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoA
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoQPlus
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoQMinus

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 7.5** (quadratic and absolute deviation risk measures).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.5, p.187 (PDF 197). The following risk measures are positive homogeneous and
subadditive:
(F) `ρ_Q(ϑ) := √(𝔼[ϑ²])`, `ϑ ∈ 𝓛²₁`;
(G) `ρ_A(ϑ) := 𝔼[|ϑ|]`, `ϑ ∈ 𝓛¹₁`;
(H) `ρ⁺_Q(ϑ) := √(𝔼[(ϑ⁺)²])` and `ρ⁻_Q(ϑ) := √(𝔼[(ϑ⁻)²])`, `ϑ ∈ 𝓛¹₁`.

**Formalization Note.** `𝓛^p₁` is `Lspace ℝ p P`. On the printed domain `𝓛¹₁` of (H) the second
moments can be infinite, so `ρ^±_Q` take values in `[0, ∞]`; their positive homogeneity reads
`ρ(λϑ) = λ ρ(ϑ)` with `λ ≥ 0` real (cast to `[0, ∞]`, `0 · ∞ = 0`) and subadditivity is in
`[0, ∞]`. On `𝓛²₁ ⊆ 𝓛¹₁` the values are finite, so this contains the real-valued statement on
`𝓛²₁`. -/
theorem proposition_7_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    (IsPosHomogeneous (fun ϑ : Lspace ℝ 2 P => rhoQ P ϑ) ∧
      IsSubadditive (fun ϑ : Lspace ℝ 2 P => rhoQ P ϑ)) ∧
    (IsPosHomogeneous (fun ϑ : Lspace ℝ 1 P => rhoA P ϑ) ∧
      IsSubadditive (fun ϑ : Lspace ℝ 1 P => rhoA P ϑ)) ∧
    ((∀ ϑ ∈ Lspace ℝ 1 P, ∀ c : ℝ, 0 ≤ c → rhoQPlus P (c • ϑ) = ENNReal.ofReal c * rhoQPlus P ϑ) ∧
      (∀ ϑ₁ ∈ Lspace ℝ 1 P, ∀ ϑ₂ ∈ Lspace ℝ 1 P,
        rhoQPlus P (ϑ₁ + ϑ₂) ≤ rhoQPlus P ϑ₁ + rhoQPlus P ϑ₂)) ∧
    ((∀ ϑ ∈ Lspace ℝ 1 P, ∀ c : ℝ, 0 ≤ c → rhoQMinus P (c • ϑ) = ENNReal.ofReal c * rhoQMinus P ϑ) ∧
      (∀ ϑ₁ ∈ Lspace ℝ 1 P, ∀ ϑ₂ ∈ Lspace ℝ 1 P,
        rhoQMinus P (ϑ₁ + ϑ₂) ≤ rhoQMinus P ϑ₁ + rhoQMinus P ϑ₂)) := by sorry

end KallMayerSLP.RiskMeasures

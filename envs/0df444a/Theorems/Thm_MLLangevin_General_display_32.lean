-- Prove2me | Theorems.Thm_MLLangevin_General_display_32
-- name    : MLLangevin.General.display_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:20.684988+00:00
-- url     : https://prove2.me/theorems/79cb45e9-47aa-4ca5-8335-f95036bc48bc
-- title:
--   (32), p. 23 — Var(𝒴) = Var(level-0 average) + Σ_{r=1}^R Var((T_r − τ)⁻¹∫_τ^{T_r} G^{γ_{r−1}}_s ds) by independence of the levels
-- statement:
--   Let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions, $b,\sigma,f$ Lipschitz, $x_0\in\mathbb R^d$, $\gamma_0>0$, $R\in\mathbb N$, $\tau\in\mathbb R$ and horizons $(T_r)_r$. Then the variance of the multilevel occupation measure splits over the levels:
--   $$\operatorname{Var}\big(\mathcal Y(R,(\gamma_r)_r,\tau,(T_r)_r,f)\big)=\operatorname{Var}\Big(\frac1{T_0-\tau}\int_\tau^{T_0}f(\bar X^{\gamma_0,x_0}_{\underline{s}_{\gamma_0}})ds\Big)+\sum_{r=1}^R\operatorname{Var}\Big(\frac1{T_r-\tau}\int_\tau^{T_r}G^{\gamma_{r-1}}_s\,ds\Big),$$
--   where $G^\gamma_s=f(\bar X^{\gamma/2,x_0}_{\underline{s}_\gamma})-f(\bar X^{\gamma,x_0}_{\underline{s}_\gamma})$ is computed with the Brownian motion of the level.
--
--   This decomposition reduces the variance study to one level at a time (Lemma 3.2 for $r\ge1$, the ergodic bound of p. 26 for $r=0$).
--
--   **Formalization Note.** Variances are `evariance`, valued in $[0,\infty]$, on both sides. The decomposition only uses the independence of the levels' Brownian motions; it is stated for arbitrary horizons and warm start.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, (32), p. 23

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem display_32 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℕ → ℝ≥0 → Ω → Rd d)
    (hB : ∀ r, EthierKurtz.IsStandardBrownian P (B r))
    (hind : iIndepFun (fun r ω => fun t => B r t ω) P)
    (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d))
    (hb : ∃ K, LipschitzWith K b) (hσ : ∃ K, LipschitzWith K σ)
    (f : Rd d → ℝ) (hf : ∃ K, LipschitzWith K f) (x₀ : Rd d)
    (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (R : ℕ) (τ : ℝ) (T : ℕ → ℝ) :
    evariance (estimator b σ x₀ γ₀ R τ T B f) P
      = ∑ r ∈ Finset.range (R + 1), evariance (levelTerm b σ x₀ γ₀ τ T B f r) P := by sorry

end MLLangevin.General

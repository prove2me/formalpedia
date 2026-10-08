-- Prove2me | Theorems.Thm_FunctionalIto_Representation_lemma_5_7
-- name    : FunctionalIto.Representation.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:32.61458+00:00
-- url     : https://prove2.me/theorems/f487d70d-0152-43f2-9375-3a2f3e19529d
-- title:
--   Lemma 5.7, p. 18 — {∇_XY : Y ∈ D(X)} is dense in 𝓛²(X) and 𝒲^{1,2}(X) = 𝓘²(X)
-- statement:
--   Under Assumption 5.1 (with $\mathcal F=\mathcal F^X$ and $E[X](T)<\infty$):
--   1. the set $\{\nabla_XY:\ Y\in D(X)\}$ is dense in $\mathcal L^2(X)$: for every $\varphi\in\mathcal L^2(X)$ and $\varepsilon>0$ there are $Y\in D(X)$ and a vertical derivative $\psi$ of $Y$ with $\|\psi-\varphi\|^2_{\mathcal L^2(X)}<\varepsilon$;
--   2. the martingale Sobolev space equals the space of square-integrable stochastic integrals:
--   $$\mathcal W^{1,2}(X)=\mathcal I^2(X).$$
--
--   Together with Proposition 5.5 this is what makes the closure of $\nabla_X$ defined on every square-integrable stochastic integral.
--
--   **Formalization Note.** The density is stated with the squared norm $E\int_0^T(\psi-\varphi)^{\top}A(\psi-\varphi)\,dt$, valued in $[0,\infty]$. The working filtration is the completed natural filtration of $X$; for a larger filtration item 1 is false.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 18, Lemma 5.7

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_FunctionalIto_Representation_Setting
import Definitions.Def_FunctionalIto_Representation_L2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

theorem lemma_5_7
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (W : ℝ≥0 → Ω → EthierKurtz.SDEState d) (𝒢 ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (X : ℝ≥0 → Ω → (Fin d → ℝ))
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (hS : IsBrownianSetting P T W 𝒢 σ X ℱ A) :
    (∀ φ : ℝ≥0 → Ω → (Fin d → ℝ), MemL2X P ℱ T A φ → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (Y : ℝ≥0 → Ω → ℝ) (ψ : ℝ≥0 → Ω → (Fin d → ℝ)),
        IsVertDerivD P ℱ T X A Y ψ ∧ L2XNormSq P T A (ψ - φ) < ε) ∧
    (∀ Y : ℝ≥0 → Ω → ℝ, MemW12 P ℱ T X A Y ↔ MemI2X P ℱ T X A Y) := by sorry

end FunctionalIto.Representation

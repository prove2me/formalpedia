-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_Supplement_theorem_9
-- name    : GenEmpLik.Coverage.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:17:21.25653+00:00
-- url     : https://prove2.me/theorems/5b0d370f-19b4-46b7-a41e-957199589604
-- title:
--   Theorem 9 — uniform variance expansion for every Donsker class
-- statement:
--   Let $H=\{h_i:i\in I\}$ be an arbitrary $P_0$-Donsker class of measurable real functions, with a nonnegative measurable envelope $M$ satisfying $|h_i(z)|\le M(z)$ for every $i,z$ and $E_{P_0}M^2<\infty$. Let $\xi_j$ be iid with law $P_0$, let $f$ satisfy Assumption A and fix $\rho\ge0$. Write $s_n^2(h)$ for the empirical variance with divisor $n$. Then
--   $$\sup_{P\ll\widehat P_n:D_f(P\|\widehat P_n)\le\rho/n}E_Ph
--   =E_{\widehat P_n}h+\sqrt{\rho s_n^2(h)/n}+\varepsilon_n(h),$$
--   $$\sup_{h\in H}\sqrt n\,|\varepsilon_n(h)|\longrightarrow0\quad\text{in outer probability}.$$
--   This is the full class expansion, including signed functions and zero-variance members. The index set may be uncountable.
--
--   **Formalization Note** The Donsker hypothesis is the uniform-norm empirical central limit theorem to a tight Borel Gaussian bridge, using outer expectations without assuming measurable empirical-process maps. The coefficient is exactly one because $f''(1)=2$. The error is defined by the displayed identity; repeated sample points are retained as indices.
--
--   Differences from the source:
--   - encoding: supremum of the scaled absolute remainder → outer probability of existence of a class member exceeding a positive threshold; reason: strict sup exceedance is equivalent to an existential exceedance; this avoids a default real supremum on an empty or unbounded class
--   - reading: distributions with divergence at most rho/n from the empirical law → sample-indexed probability weights in the published divergence ball; reason: (4a), (15) and (31) specify absolute continuity; tied observations retain separate indices and can be averaged by convexity
--   - encoding: random losses and iid observations → explicit measurability, independence and equality in distribution; reason: random variables in Section 2 are measurable; no measurability is imposed on supremum events
--   - reading: the preceding paragraph prints h at most M → absolute domination |h| at most M; reason: envelope has this meaning, explicitly confirmed by Lemma 14 on p. 35
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 22, Theorem 9; absolute envelope also Lemma 14, p. 35; proof p. 36

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_Supplement_DonskerClass
import Definitions.Def_GenEmpLik_Coverage_Supplement_uniformRemainder

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GenEmpLik.Coverage.Supplement

/-- Theorem 9, p. 22: uniform expansion for an arbitrary Donsker class with
an absolute L² envelope (the absolute value is explicit in Lemma 14, p. 35). -/
theorem theorem_9
    {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (h : ι → Ξ → ℝ) (M : Ξ → ℝ)
    (f : ℝ → EReal) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hA : GenEmpLik.Coverage.AssumptionA f)
    (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (hM : Measurable M) (hMnonneg : ∀ z, 0 ≤ M z)
    (henvelope : ∀ i z, |h i z| ≤ M z)
    (hM2 : Integrable (fun z => M z ^ 2) (μ.map (ξ 0)))
    (hDonsker : IsDonsker μ (μ.map (ξ 0)) ξ h) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω | ∃ j : ι,
      δ < Real.sqrt (n : ℝ) *
        |uniformRemainder f ρ (fun i : Fin n => h j (ξ i ω))|}) atTop (𝓝 0) := by sorry

end GenEmpLik.Coverage.Supplement

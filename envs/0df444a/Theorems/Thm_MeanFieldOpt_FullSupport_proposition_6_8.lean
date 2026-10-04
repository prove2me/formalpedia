-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_proposition_6_8
-- name    : MeanFieldOpt.FullSupport.proposition_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:10:46.116872+00:00
-- url     : https://prove2.me/theorems/7a7a0975-28d7-4e27-b3b7-11ba4b6006e5
-- title:
--   Proposition 6.8 — first variation $\frac{d}{ds}\mathsf P(\gamma+s\delta)|_{s=0+}=\frac12\int_0^1\xi''\delta(\mathbb E\{\partial_x\Phi(t,X_t)^2\}-t)dt$
-- statement:
--   Let $\xi$ be a mixture, $f_0$ an admissible terminal condition, and $\gamma \in \mathscr L$. Let $\delta : [0,1) \to \mathbb R$ satisfy
--
--   1. $\|\xi''\delta\|_{\mathrm{TV}[0,t]} < \infty$ for all $t \in [0,1)$;
--   2. $\|\xi''\delta\|_1 < \infty$;
--   3. $\delta(t) = 0$ for $t \in (1-\varepsilon, 1)$, for some $\varepsilon > 0$;
--   4. $\gamma + s\delta \ge 0$ for all $s \in [0, s_0)$, for some $s_0 > 0$.
--
--   Let $X$ be the strong solution of the SDE (6.3) for $\gamma$, driven by a standard Brownian motion, and $\Phi = \Phi^\gamma$. Then the right derivative of the Parisi functional along $\gamma + s\delta$ at $s = 0$ exists and equals
--
--   $$
--   \frac{d\mathsf P}{ds}(\gamma + s\delta)\Big|_{s=0+} = \frac12 \int_0^1 \xi''(t)\,\delta(t)\,\bigl(\mathbb E\{\partial_x\Phi(t, X_t)^2\} - t\bigr)\,dt .
--   $$
--
--   This first-variation formula is the source of the stationarity conditions satisfied by a minimizer.
--
--   **Formalization Note** The right derivative is `HasDerivWithinAt … (Set.Ici 0) 0` of $s \mapsto \mathsf P(\gamma + s\delta)$; the functional is the one with terminal condition $f_0$. Condition 3 is stated on $[0,1)$, the domain of $\delta$. The process $X$ solves (6.3) for $\gamma$ (not for $\gamma + s\delta$).
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 27, Proposition 6.8, Eq. (6.9)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiP
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MeanFieldOpt.FullSupport

/-- Proposition 6.8 (arXiv:2001.00904v1, p. 27): first variation of the Parisi functional. For
`γ ∈ ℒ` and a perturbation `δ` with `‖ξ''δ‖_{TV[0,t]} < ∞` for `t ∈ [0,1)`, `‖ξ''δ‖₁ < ∞`,
`δ = 0` on `(1 - ε, 1)` for some `ε > 0`, and `γ + sδ ≥ 0` for `s ∈ [0, s₀)`,
`(d/ds) P(γ + sδ)|_{s=0+} = (1/2) ∫_0^1 ξ''(t) δ(t) (E{∂_xΦ(t, X_t)²} - t) dt`, where `X`
solves (6.3) for `γ`. -/
theorem proposition_6_8 (ξ : Mixture) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀) (γ : ℝ → ℝ)
    (hγ : InL ξ γ) (δ : ℝ → ℝ)
    (hδTV : ∀ t ∈ Set.Ico (0 : ℝ) 1, eVariationOn (fun s => ξ.d2 s * δ s) (Set.Icc 0 t) ≠ ⊤)
    (hδint : IntegrableOn (fun s => ξ.d2 s * δ s) (Set.Ico 0 1))
    (hδend : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (0 : ℝ) 1, 1 - ε < t → δ t = 0)
    (hpos : ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s ∈ Set.Ico (0 : ℝ) s₀, ∀ t ∈ Set.Ico (0 : ℝ) 1,
      0 ≤ γ t + s * δ t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W X : ℝ≥0 → Ω → EthierKurtz.SDEState 1) (hW : IsBrownianReal (fun t ω => W t ω 0) P)
    (hX : IsParisiSDESol ξ f₀ γ P W X) :
    HasDerivWithinAt (fun s : ℝ => ParisiP ξ f₀ (fun t => γ t + s * δ t))
      ((1 / 2) * ∫ t in Set.Ico (0 : ℝ) 1,
        ξ.d2 t * δ t * ((∫ ω, (deriv (PhiL ξ f₀ γ t) (pathAt X t ω)) ^ 2 ∂P) - t))
      (Set.Ici 0) 0 := by sorry

end MeanFieldOpt.FullSupport

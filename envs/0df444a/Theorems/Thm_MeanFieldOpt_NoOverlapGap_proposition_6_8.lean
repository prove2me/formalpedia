-- Prove2me | Theorems.Thm_MeanFieldOpt_NoOverlapGap_proposition_6_8
-- name    : MeanFieldOpt.NoOverlapGap.proposition_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:08:24.946505+00:00
-- url     : https://prove2.me/theorems/9830aabc-f7f6-4916-b5ac-91d19d2f8305
-- title:
--   Proposition 6.8 — first variation of the Parisi functional on $\mathscr L$
-- statement:
--   Let $\xi$ be a mixture and $\gamma \in \mathscr L$. Let $\delta : [0,1) \to \mathbb R$ satisfy
--
--   1. $\|\xi''\delta\|_{TV[0,t]} < \infty$ for every $t \in [0,1)$;
--   2. $\|\xi''\delta\|_1 = \int_0^1 \xi''(t)|\delta(t)|\,dt < \infty$;
--   3. $\delta(t) = 0$ for $t \in (1-\varepsilon, 1)$, for some $\varepsilon > 0$;
--   4. $\gamma + s\delta \ge 0$ on $[0,1)$ for all $s \in [0, s_0)$, for some $s_0 > 0$.
--
--   Let $\Phi = \Phi^\gamma$ and let $(X_t)_{t\in[0,1]}$ be the solution of the SDE (6.3) for $\gamma$, driven by a standard Brownian motion. Then $s \mapsto \mathsf P(\gamma + s\delta)$ has a right derivative at $s = 0$, equal to
--
--   $$\frac{d\mathsf P}{ds}(\gamma + s\delta)\Big|_{s=0+} = \frac12 \int_0^1 \xi''(t)\,\delta(t)\,\Big( \mathbb E\{\partial_x\Phi(t,X_t)^2\} - t \Big)\,dt .$$
--
--   This first-variation formula is the source of every stationarity condition satisfied by minimisers of $\mathsf P$, over $\mathscr L$ or over $\mathscr U$.
--
--   **Formalization Note** The right derivative is `HasDerivWithinAt` on $[0,\infty)$ at $0$. Conditions 1–2 are stated with `eVariationOn` and `IntegrableOn` on $[0,1)$; condition 3 constrains $\delta$ only on $(1-\varepsilon,1)$, since $\delta$ lives on $[0,1)$ (the paper writes $(1-\varepsilon,1]$). The process $X$ solves the SDE for $\gamma$, not for $\gamma + s\delta$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 27, Proposition 6.8, Eq. (6.9)

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Spaces
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Parisi
import Definitions.Def_MeanFieldOpt_NoOverlapGap_SDE

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MeanFieldOpt.NoOverlapGap

/-- Proposition 6.8 (arXiv:2001.00904v1, p. 27): the right derivative of `s ↦ P(γ + sδ)` at
`s = 0` is `(1/2) ∫_0^1 ξ''(t) δ(t) (E{∂_xΦ(t, X_t)²} − t) dt`, where `X` solves (6.3) for `γ`. -/
theorem proposition_6_8 (ξ : Mixture) (γ δ : ℝ → ℝ) (hγ : InL ξ γ)
    (hδTV : ∀ t ∈ Ico (0 : ℝ) 1, eVariationOn (fun s => ξ.xi'' s * δ s) (Icc 0 t) ≠ ⊤)
    (hδ1 : IntegrableOn (fun s => ξ.xi'' s * δ s) (Ico (0 : ℝ) 1))
    (hδε : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (1 - ε) 1, δ t = 0)
    (hpos : ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s ∈ Ico (0 : ℝ) s₀, ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ γ t + s * δ t)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B X : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B Pr) (hX : SolvesParisiSDE ξ γ Pr B X) :
    HasDerivWithinAt (fun s : ℝ => P ξ (γ + s • δ))
      ((1 / 2) * ∫ t in Ico (0 : ℝ) 1, ξ.xi'' t * δ t *
        ((∫ ω, (deriv (fun y => PhiL ξ γ t y) (X t.toNNReal ω)) ^ 2 ∂Pr) - t))
      (Ici 0) 0 := by sorry

end MeanFieldOpt.NoOverlapGap

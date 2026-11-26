-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_lemma_2
-- name    : OnlineUBSR.Supplement.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:39:36.924904+00:00
-- url     : https://prove2.me/theorems/8f8c70b7-50fe-4b39-b5ac-0fbaee221d2e
-- title:
--   Lemma 2 (corrected: $L_3$ made explicit) — second-derivative bound
-- statement:
--   Under Assumptions 1–3 and 5–9 uniformly over $\theta\in[\theta_l,\theta_u]$, and with $|\xi''(\theta)|\le L_3$ almost surely, the UBSR objective satisfies
--   $$|h''(\theta)|\le L_4=\frac{2L_1L_2M_2^2+2L_1L_2B_1M_2+L_1^2L_3}{\eta^2}$$
--   throughout the interval, where $B_1=L_1M_2/\eta$.
--
--   Differences from the source:
--   - correction: Assumption 3 bounds $-\ell'(-t)$ → Lean bounds $g_\theta'(t)$; reason: the derivative formula for shortfall risk uses $g_\theta'$
--   - correction: $L_3$ is named but no assumption defines it → Lean assumes $|\xi''(\theta)|\le L_3$ almost surely; reason: this is exactly the bound used in the proof on p.27
--   - encoding: the source treats $h''$ as an ordinary derivative → Lean explicitly requires differentiability of $h$ and $h'$ on the interval; reason: this excludes the default value of `deriv` at nondifferentiability points
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 2, p.27, equation (57)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory Real

namespace OnlineUBSR.Supplement

/-- **Lemma 2 (uniform second-derivative bound).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 2, p.27, (57).

**Formalization Note.** The paper mentions `L₃` in the statement without defining it. Its proof
uses exactly `|ξ''(θ)|≤L₃`, which is the explicit hypothesis here. The second derivative is
`deriv (deriv h)` and `SmoothObjective` makes that notation non-junk on the interval. -/
theorem lemma_2
    {E : Type*} [MeasurableSpace E] (M : Model E) [IsProbabilityMeasure M.ν]
    (h123 : Assumptions1To3 M) (h59 : Assumptions5To9 M)
    (hsmooth : SmoothObjective M) (L₃ : ℝ) (hL₃ : 0 ≤ L₃)
    (hFsecond : ∀ θ ∈ Set.Icc M.θl M.θu,
      ∀ᵐ u ∂M.ν, |deriv (deriv (fun q => M.F q u)) θ| ≤ L₃) :
    ∀ θ ∈ Set.Icc M.θl M.θu, |deriv (deriv (objective M)) θ| ≤ L4 M L₃ := by sorry

end OnlineUBSR.Supplement

-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_sum_integral_eq_zero_of_null_homology
-- name    : OAI.CrouzeixHilbert.sum_integral_eq_zero_of_null_homology
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:34:32.481834+00:00
-- url     : https://prove2.me/theorems/7f2dbefd-9b56-412d-ac48-18f2da97a86f
-- title:
--   Cauchy's integral theorem, homology form, for finitely many smooth closed contours with vanishing total winding number outside an open set
-- statement:
--   A smooth contour (`SmoothContour`, from the published bundle `Def_CrouzeixHilbert`) is a map $\gamma : \mathbb R \to \mathbb C$ (`path`) that is continuously differentiable (`ContDiff ℝ 1 path`) with $\gamma(0) = \gamma(1)$; its winding number about $w \in \mathbb C$ (`SmoothContour.index`, from the same bundle) is
--   $$\operatorname{ind}_\gamma(w) = \frac{1}{2\pi i}\int_0^1 \frac{\gamma'(t)}{\gamma(t) - w}\,dt .$$
--
--   Let $\iota$ be a finite type (`Fintype ι`), let $E$ be a complex Banach space (`NormedAddCommGroup E`, `NormedSpace ℂ E`, `CompleteSpace E`), let $\gamma_i$ ($i \in \iota$) be smooth contours and $c_i \in \mathbb C$, and let $U \subseteq \mathbb C$ be open (`IsOpen U`). Suppose that
--   - the image $\gamma_i([0,1])$ of every contour lies in $U$ (`(Γ i).path '' Set.Icc 0 1 ⊆ U`); and
--   - the chain $\sum_i c_i \gamma_i$ has total winding number zero about every point outside $U$: $\sum_i c_i \operatorname{ind}_{\gamma_i}(w) = 0$ for every $w \notin U$.
--
--   Let $f : \mathbb C \to E$ be complex differentiable on $U$ (`DifferentiableOn ℂ f U`). Then
--   $$\sum_{i} c_i\,\frac{1}{2\pi i}\int_0^1 \gamma_i'(t)\, f\bigl(\gamma_i(t)\bigr)\,dt \;=\; 0,$$
--   where $\gamma_i'$ is `deriv (Γ i).path`, the integral is the interval integral `∫ t in (0:ℝ)..1`, and the scalar factors act on $E$ by `•`.
--
--   This is the homology form of Cauchy's integral theorem (Cauchy, 1825; homology form as in Artin, 1944), with vector values.
--
--   Lean: `OAI.CrouzeixHilbert.sum_integral_eq_zero_of_null_homology`. OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/HomologicalCauchy.lean`) states the same with OpenAI's `SmoothContour.trace` (the image $\gamma([0,1])$) and `SmoothContour.integral` (the normalized integral above); here both are written out, so the statement needs only the published bundle `Def_CrouzeixHilbert` for `SmoothContour` and `SmoothContour.index`.
-- source:
--   A.-L. Cauchy, Mémoire sur les intégrales définies prises entre des limites imaginaires (1825) (the theorem); homology form as in E. Artin (1944), with the proof of J. D. Dixon, A brief proof of Cauchy's integral theorem, Proc. Amer. Math. Soc. 29 (1971), 625–626; proof and Lean code: OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/HomologicalCauchy.lean (declaration OAI.CrouzeixHilbert.sum_integral_eq_zero_of_null_homology)

import Mathlib
import Definitions.Def_CrouzeixHilbert

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology

namespace CrouzeixHilbert

theorem sum_integral_eq_zero_of_null_homology {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).path '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ∑ i, c i • ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∫ t in (0 : ℝ)..1, deriv (Γ i).path t • f ((Γ i).path t)) = 0 := by
  sorry

end CrouzeixHilbert

end

end OAI
end

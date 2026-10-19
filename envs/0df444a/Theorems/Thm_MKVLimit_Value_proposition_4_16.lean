-- Prove2me | Theorems.Thm_MKVLimit_Value_proposition_4_16
-- name    : MKVLimit.Value.proposition_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:34.909896+00:00
-- url     : https://prove2.me/theorems/6d2f161f-7c42-4ad0-b174-ebc4afefb29e
-- title:
--   Proposition 4.16 (value bound), p. 31
-- statement:
--   Let $\nu^m$ converge to $\nu$ in $\mathcal W_p$, with uniformly bounded $p'$th moments of $\nu^m$ and finite $p$th moment of $\nu$. Then
--
--   $$V_S(\nu)\le\liminf_{m\to\infty}V_S(\nu^m).$$
--
--   This is the lower value bound used for stability of the limiting strong-control problem.
--
--   **Formalization Note** This item formalizes the final value clause of Proposition 4.16; its law-convergence clause is not asserted here. Assumption 2.1 and the Euclidean-control condition from the section apply. Lean index zero denotes the paper's first sequence element.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, p. 31, Proposition 4.16, final value clause

import Definitions.Def_MKVLimit_Value_Particle

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

/-- Proposition 4.16, final value bound, p. 31. Lean index 0 is ν¹. -/
theorem proposition_4_16 {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [PolishSpace U]
    (hT : 0 < T) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (M : Model T n d ℓ U) (p p' : ℝ) (hA21 : Assumption21 M p p')
    (hAj : AEmbedsEuclid U)
    (Pν : ProbabilityMeasure (Rn n) → Measure (OmegaS T n d ℓ))
    (hPν : ∀ ν, IsStrongLaw ν (Pν ν))
    (ν : ProbabilityMeasure (Rn n)) (hν : HasMoment p ν)
    (νm : ℕ → ProbabilityMeasure (Rn n)) (hνm : ∀ m, HasMoment p' (νm m))
    (hbdd : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ m,
      (∫⁻ x, ‖x‖ₑ ^ p' ∂(νm m : Measure (Rn n))) ≤ K)
    (hconv : Tendsto (fun m => Wp p (νm m) ν) atTop (𝓝 0)) :
    VS M p ν (Pν ν) ≤
      liminf (fun m => VS M p (νm m) (Pν (νm m))) atTop := by sorry

end MKVLimit.Value

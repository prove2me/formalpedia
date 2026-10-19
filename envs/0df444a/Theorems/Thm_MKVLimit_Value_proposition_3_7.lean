-- Prove2me | Theorems.Thm_MKVLimit_Value_proposition_3_7
-- name    : MKVLimit.Value.proposition_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:37.353473+00:00
-- url     : https://prove2.me/theorems/26fb8ad1-354d-4803-a7f8-ed146a9768b6
-- title:
--   Proposition 3.7, equation (3.4), p. 13
-- statement:
--   Assume the paper's regularity and marginal-dependence conditions, a Euclidean control space, and continuity of the reward coefficients. If $\nu^m\to\nu$ in $\mathcal W_p$ and the $p'$th moments of the $\nu^m$ are uniformly bounded, then
--
--   $$V_S(\nu^m)\longrightarrow V_S(\nu).$$
--
--   This stability statement transfers value convergence between nearby initial laws.
--
--   **Formalization Note** This item states equation (3.4), with values in the extended reals. The subsequent “In particular” continuity sentence is omitted because it needs a separate topology choice on $\mathcal P_{p'}$. Lean index zero denotes the paper's first sequence element.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, p. 13, Proposition 3.7, equation (3.4)

import Definitions.Def_MKVLimit_Value_Particle

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

/-- Proposition 3.7, equation (3.4), p. 13. Lean index 0 is ν¹. -/
theorem proposition_3_7 {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [PolishSpace U]
    (hT : 0 < T) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (M : Model T n d ℓ U) (p p' : ℝ) (hA21 : Assumption21 M p p')
    (hA212 : Assumption212 M) (hAj : AEmbedsEuclid U)
    (hLg : IsContinuousLg M p)
    (Pν : ProbabilityMeasure (Rn n) → Measure (OmegaS T n d ℓ))
    (hPν : ∀ ν, IsStrongLaw ν (Pν ν))
    (ν : ProbabilityMeasure (Rn n)) (hν : HasMoment p ν)
    (νm : ℕ → ProbabilityMeasure (Rn n)) (hνm : ∀ m, HasMoment p' (νm m))
    (hbdd : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ m,
      (∫⁻ x, ‖x‖ₑ ^ p' ∂(νm m : Measure (Rn n))) ≤ K)
    (hconv : Tendsto (fun m => Wp p (νm m) ν) atTop (𝓝 0)) :
    Tendsto (fun m => VS M p (νm m) (Pν (νm m)))
      atTop (𝓝 (VS M p ν (Pν ν))) := by sorry

end MKVLimit.Value

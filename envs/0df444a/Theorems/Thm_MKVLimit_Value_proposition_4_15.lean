-- Prove2me | Theorems.Thm_MKVLimit_Value_proposition_4_15
-- name    : MKVLimit.Value.proposition_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:32.485532+00:00
-- url     : https://prove2.me/theorems/b529f41d-d763-4a26-a75a-8e0b1404a632
-- title:
--   Proposition 4.15 (value bound), p. 29
-- statement:
--   Let $\nu$ be an initial law with finite $p$th moment, and let $(\nu^i)_{i\ge1}$ have uniformly bounded average $p'$th moments, where $p'>p\ge2$. If their averaged laws converge to $\nu$ in $\mathcal W_p$, then
--
--   $$V_S(\nu)\le\liminf_{N\to\infty}V_S^N(\nu^1,\ldots,\nu^N).$$
--
--   This is the lower value bound for the particle approximation.
--
--   **Formalization Note** This item formalizes only the final “Consequently” clause of Proposition 4.15, under Assumption 2.1 and the section's Euclidean-control hypothesis. The preceding law-convergence clauses are outside this item. Lean player index zero is $\nu^1$; the extended-real liminf does not assign a default finite value.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, p. 29, Proposition 4.15, final displayed inequality

import Definitions.Def_MKVLimit_Value_Particle

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

/-- Proposition 4.15, final value bound, p. 29. Lean player 0 is ν¹. -/
theorem proposition_4_15 {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [PolishSpace U]
    (hT : 0 < T) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (M : Model T n d ℓ U) (p p' : ℝ) (hA21 : Assumption21 M p p')
    (hAj : AEmbedsEuclid U)
    (Pν : ProbabilityMeasure (Rn n) → Measure (OmegaS T n d ℓ))
    (hPν : ∀ ν, IsStrongLaw ν (Pν ν))
    (PN : (N : ℕ+) → (Fin N → ProbabilityMeasure (Rn n)) → Measure (OmegaN T n d ℓ N))
    (hPN : ∀ N ν, IsParticleLaw N ν (PN N ν))
    (ν : ProbabilityMeasure (Rn n)) (hν : HasMoment p ν)
    (νi : ℕ → ProbabilityMeasure (Rn n)) (hνi : ∀ i, HasMoment p' (νi i))
    (hbdd : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ N : ℕ+,
      (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N,
        ∫⁻ x, ‖x‖ₑ ^ p' ∂(νi i : Measure (Rn n)) ≤ K)
    (hconv : Tendsto (fun N : ℕ+ => Wp p (avgLaw N νi) ν) atTop (𝓝 0)) :
    VS M p ν (Pν ν) ≤
      liminf (fun N : ℕ+ => VSN M p N (PN N (fun i => νi i))) atTop := by sorry

end MKVLimit.Value

-- Prove2me | Theorems.Thm_MKVLimit_Value_theorem_3_6_iii
-- name    : MKVLimit.Value.theorem_3_6_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:39.846907+00:00
-- url     : https://prove2.me/theorems/14bbf7d3-0624-4ab3-83db-28cc7b7f95d5
-- title:
--   Theorem 3.6(iii), equation (3.3), p. 12
-- statement:
--   Let the initial laws $(\nu^i)_{i\ge1}$ have uniformly bounded average $p'$th moments, where $p'>p\ge2$. Under Assumptions 2.1 and 2.12, a Euclidean control embedding, and continuity of $L$ and $g$, the $N$-player optimal value approaches the strong McKean–Vlasov value at the averaged initial law:
--
--   $$\lim_{N\to\infty}\left|V_S^N(\nu^1,\ldots,\nu^N)-V_S\!\left(\frac1N\sum_{i=1}^N\nu^i\right)\right|=0.$$
--
--   The averaged laws themselves need not converge; the theorem compares the two values at each positive $N$.
--
--   **Formalization Note** The statement explicitly requires both extended-real values to be finite for every $N$, so the displayed real absolute difference is well defined. The strong and particle laws are characterized Brownian laws on their canonical spaces, not arbitrary measures. Conditional and empirical laws are tied to the solutions. Lean player zero is the paper's player one. Continuity uses the disclosed sequential $\mathcal W_p$ reading.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, p. 12, Theorem 3.6(iii), equation (3.3); proof p. 34

import Definitions.Def_MKVLimit_Value_Particle

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

/-- Theorem 3.6(iii), equation (3.3), p. 12. Lean player 0 is ν¹. -/
theorem theorem_3_6_iii {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [PolishSpace U]
    (hT : 0 < T) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (M : Model T n d ℓ U) (p p' : ℝ) (hA21 : Assumption21 M p p')
    (hA212 : Assumption212 M) (hAj : AEmbedsEuclid U)
    (hLg : IsContinuousLg M p)
    (Pν : ProbabilityMeasure (Rn n) → Measure (OmegaS T n d ℓ))
    (hPν : ∀ ν, IsStrongLaw ν (Pν ν))
    (PN : (N : ℕ+) → (Fin N → ProbabilityMeasure (Rn n)) → Measure (OmegaN T n d ℓ N))
    (hPN : ∀ N ν, IsParticleLaw N ν (PN N ν))
    (ν : ℕ → ProbabilityMeasure (Rn n)) (hν : ∀ i, HasMoment p' (ν i))
    (hbdd : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ N : ℕ+,
      (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N,
        ∫⁻ x, ‖x‖ₑ ^ p' ∂(ν i : Measure (Rn n)) ≤ K) :
    (∀ N : ℕ+, VSN M p N (PN N (fun i => ν i)) ≠ ⊤ ∧
      VSN M p N (PN N (fun i => ν i)) ≠ ⊥ ∧
      VS M p (avgLaw N ν) (Pν (avgLaw N ν)) ≠ ⊤ ∧
      VS M p (avgLaw N ν) (Pν (avgLaw N ν)) ≠ ⊥) ∧
    Tendsto (fun N : ℕ+ =>
      |(VSN M p N (PN N (fun i => ν i))).toReal -
        (VS M p (avgLaw N ν) (Pν (avgLaw N ν))).toReal|)
      atTop (𝓝 0) := by sorry

end MKVLimit.Value

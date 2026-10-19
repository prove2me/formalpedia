-- Prove2me | Theorems.Thm_MKVLimit_Value_eq_4_44
-- name    : MKVLimit.Value.eq_4_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:43.548843+00:00
-- url     : https://prove2.me/theorems/9967ecbb-0531-46ba-ac94-382d57f7a114
-- title:
--   Equation (4.44), p. 34 (subsequence form)
-- statement:
--   Under the hypotheses of Theorem 3.6, take a strictly increasing subsequence of particle counts $N_m$ for which the averaged initial laws converge in $\mathcal W_p$ to a law $\nu$ with finite $p$th moment. The strong-value clause of equation (4.44) says
--
--   $$V_S^{N_m}(\nu^1,\ldots,\nu^{N_m})\longrightarrow V_S(\nu).$$
--
--   This subsequence limit is the value statement used inside the proof of Theorem 3.6(iii).
--
--   **Formalization Note** The display printed as (4.44) uses a full-sequence limit although its proof has selected a subsequence; this item states the subsequence conclusion the proof uses. The equalities through the relaxed value and limiting relaxed reward are not part of this item. The strong value is explicitly finite. Lean player index zero is $\nu^1$.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, p. 34, proof of Theorem 3.6(i), equation (4.44)

import Definitions.Def_MKVLimit_Value_Particle

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

/-- The strong-value clause of (4.44), in the subsequence form used in the proof, p. 34. -/
theorem eq_4_44 {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [PolishSpace U]
    (hT : 0 < T) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (M : Model T n d ℓ U) (p p' : ℝ) (hA21 : Assumption21 M p p')
    (hA212 : Assumption212 M) (hAj : AEmbedsEuclid U)
    (hLg : IsContinuousLg M p)
    (Pν : ProbabilityMeasure (Rn n) → Measure (OmegaS T n d ℓ))
    (hPν : ∀ ν, IsStrongLaw ν (Pν ν))
    (PN : (N : ℕ+) → (Fin N → ProbabilityMeasure (Rn n)) → Measure (OmegaN T n d ℓ N))
    (hPN : ∀ N ν, IsParticleLaw N ν (PN N ν))
    (νi : ℕ → ProbabilityMeasure (Rn n)) (hνi : ∀ i, HasMoment p' (νi i))
    (hbdd : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ N : ℕ+,
      (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N,
        ∫⁻ x, ‖x‖ₑ ^ p' ∂(νi i : Measure (Rn n)) ≤ K)
    (Nm : ℕ → ℕ+) (hNm : StrictMono Nm)
    (ν : ProbabilityMeasure (Rn n)) (hν : HasMoment p ν)
    (hconv : Tendsto (fun m => Wp p (avgLaw (Nm m) νi) ν) atTop (𝓝 0)) :
    VS M p ν (Pν ν) ≠ ⊤ ∧ VS M p ν (Pν ν) ≠ ⊥ ∧
    Tendsto (fun m => VSN M p (Nm m) (PN (Nm m) (fun i => νi i)))
      atTop (𝓝 (VS M p ν (Pν ν))) := by sorry

end MKVLimit.Value

-- Prove2me | Theorems.Thm_InterpOptStop_SAA_Supplement_theorem_2
-- name    : InterpOptStop.SAA.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:47:43.563244+00:00
-- url     : https://prove2.me/theorems/9b4fb529-bddf-40cb-b942-744779e445da
-- title:
--   Theorem 2 (corrected: Assumption 3 codomain) — finite-depth ε-optimal trees
-- statement:
--   Consider the finite positive-horizon stopping model with deterministic initial state $\bar x$, discount $\beta\in[0,1]$ and measurable rewards. Assume the bounded product state space of Assumption 1, rewards $0\le g\le G$ of Assumption 2 and the repaired physical marginal control of Assumption 3. Assume also Assumption 4: time is available as $t/T$, and there is an admissible policy attaining the unrestricted stopping optimum whose stopping region is compact for each $t>1$. For every $\epsilon>0$ there is a finite tree policy such that
--   $$J^*(\bar x)-J^{\pi_{\rm tree}}(\bar x)\le\epsilon.$$
--   The optimum is over all measurable time-dependent policies. There is no Markov or Lipschitz premise and no quantitative depth bound in this result. Immediate stopping and $G=0$ are included. This companion theorem gives approximation to the unrestricted stopping problem.
--
--   Differences from the source:
--   - reading: expected discounted reward under the finite-horizon stochastic model → measurable policies and rewards and 0≤β≤1; all time-dependent policies enter the unrestricted supremum; reason: expectations require measurability; discounting and the proof on ec22 supply the discount range; bounded rewards make the supremum finite
--   - correction: Assumption 3 has strictly increasing f:[0,∞)→[0,1] on all finite volumes → f:[0,∞)→ℝ, with the same monotonicity, continuity, f(0)=0 and bound on measurable finite-volume physical sets; reason: p.9 describes bounded densities, giving f(r)=cr; a bounded state space forces f≥1 on a half-line and contradicts the printed strict increase and codomain; the clock is explicitly ignored on ec22
--   - encoding: periods t=1,…,T and time coordinate t/T → k : Fin T and clockState k x=((k+1)/T,x), with the published J and finite Tree (n+1); reason: zero indexing preserves the discount β^(t−1); physical dimension in every bound remains n
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Theorem 2, p. 13

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_TimedStopping

open MeasureTheory

namespace InterpOptStop.SAA.Supplement

theorem theorem_2 {n T : ℕ} (hT : 0 < T)
    (xbar : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (hXtb : TotallyBounded X) (hXdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ 1)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hstart : ∀ᵐ x ∂μ, x ⟨0, hT⟩ = xbar) (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (hgm : ∀ k, Measurable (g k))
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousOn f (Set.Ici 0))
    (hA3 : ∀ A : Set (Fin n → ℝ), MeasurableSet A → volume A ≠ ⊤ →
      ∀ k : Fin T, k.val ≠ 0 → (μ {x | x k ∈ A}).toReal ≤ f (volume A).toReal)
    (hA4 : ∃ π : TimedPolicy n T, Admissible π ∧
      timedValue μ β g π = optimalValue μ β g ∧
      ∀ k : Fin T, k.val ≠ 0 → IsCompact {x | x ∈ X ∧ π k x = Act.stop}) :
    ∀ ε : ℝ, 0 < ε → ∃ (S : Tree (n + 1)) (θ : Thresholds),
      optimalValue μ β g - treeValue μ β g S θ ≤ ε := by sorry

end InterpOptStop.SAA.Supplement

-- Prove2me | Theorems.Thm_ImpulseNMFG_Verification_lemma_2_3
-- name    : ImpulseNMFG.Verification.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:37.054667+00:00
-- url     : https://prove2.me/theorems/9a4addfd-7cce-4b33-bac5-91a849ac1954
-- title:
--   Lemma 2.3, p. 5 — controlled-process representation, continuity, jumps and action avoidance
-- statement:
--   Let $x\in S$ and let $\varphi$ be a profile of strategies with pairwise disjoint action regions. Construct the controlled process $X$ from diffusion pieces as in Definition 2.2. Before the exit time $\tau_S$, $X$ follows the current diffusion piece and is right-continuous. It is continuous away from interventions, and at positive times that are not intervention times it lies outside every action region. At player $i$'s $k$th intervention, the pre-intervention state belongs to $A_i$ and the applied impulse is $\xi_i$ evaluated there. If no further intervention occurs at that instant, the post-intervention state is the shift by $\Gamma^i$.
--
--   These path properties connect the recursively constructed state to the game cost and to the QVI regions used in the verification proof.
--
--   **Formalization Note** Equation (2.3) is expressed as a finite-stage sum when the number of stages is finite; the infinite-stage path is already the limit in the model definition. The printed claim that every pre-state lies on $\partial A_i$ is corrected to membership in closed $A_i$; the jump formula needs the no-following-intervention condition because Remark 2.10 permits consecutive jumps at one instant. Continuity and avoidance are stated before $\tau_S$; avoidance is stated for $s>0$, since $x$ may lie in some $A_i$ without an intervention at time $0$ (entry times are infima over $s>\tilde\tau_{k-1}$). Diffusion pieces satisfy the published `SolvesFrom` relation.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, p. 5, Lemma 2.3, (2.3)–(2.4)

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State)

namespace ImpulseNMFG.Verification
noncomputable section

/-- Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls,
arXiv:1901.08085v4, p. 5, Lemma 2.3, (2.3)–(2.4).
The published SolvesFrom defines the diffusion pieces, and the controlled path is built stagewise.
At a shared instant consecutive interventions can occur, so the jump identity is asserted
when no further intervention follows at that same time. The pre-state is in the closed
A_i, rather than necessarily its frontier; the latter printed claim fails at time zero.
Avoidance of action regions is asserted at positive times before τ_S that are not intervention
times: at s = 0 the initial state x may lie in A_i without an intervention at time 0 (entry
times are infima over s > τ̃_{k−1}, Definition 2.2), e.g. A_i = {x} and a path that leaves x. -/
theorem lemma_2_3 {N d M : ℕ} [NeZero N] {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin M → ℝ))
    (G : Game N d M) (x : State d) (hx : x ∈ G.S) (π : Profile G)
    (hstrat : ∀ i, IsStrategy G i (π.A i) (π.ξ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (π.A i) (π.A j))
    (Y : ℕ → ℝ≥0 → Ω → State d)
    (hY : IsRealization P 𝔽 W G x π Y) :
    ∀ ω,
      (∀ s : ℝ≥0, kbar G x π (pathOf Y ω) ≠ ⊤ →
        ctrl G x π (pathOf Y ω) s =
          (∑ k ∈ Finset.range (kbar G x π (pathOf Y ω)).toNat,
            if (stage G x π (pathOf Y ω) k).time ≤ (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) < (stage G x π (pathOf Y ω) (k + 1)).time
            then Y k s ω else 0) +
          (if (stage G x π (pathOf Y ω) (kbar G x π (pathOf Y ω)).toNat).time ≤
                (s : ℝ≥0∞)
            then Y (kbar G x π (pathOf Y ω)).toNat s ω else 0)) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < exitTime G x π (pathOf Y ω) →
        ContinuousWithinAt (ctrl G x π (pathOf Y ω)) (Set.Ici s) s) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < exitTime G x π (pathOf Y ω) →
        (s : ℝ≥0∞) ∉ interventionTimes G x π (pathOf Y ω) →
        ContinuousAt (ctrl G x π (pathOf Y ω)) s ∧
        (0 < s → ∀ i, ctrl G x π (pathOf Y ω) s ∉ π.A i)) ∧
      (∀ (i : Fin N) (n : ℕ), 1 ≤ n →
        interTime G x π (pathOf Y ω) i n < exitTime G x π (pathOf Y ω) →
        preState G x π (pathOf Y ω) i n ∈ π.A i ∧
        impulse G x π (pathOf Y ω) i n =
          π.ξ i (preState G x π (pathOf Y ω) i n) ∧
        ((∀ (j : Fin N) (k : ℕ), 1 ≤ k →
          interTime G x π (pathOf Y ω) j k =
            interTime G x π (pathOf Y ω) i n → j = i ∧ k = n) →
          ctrl G x π (pathOf Y ω)
              (interTime G x π (pathOf Y ω) i n).toNNReal =
            G.Γ i (preState G x π (pathOf Y ω) i n)
              (impulse G x π (pathOf Y ω) i n))) := by sorry

end
end ImpulseNMFG.Verification

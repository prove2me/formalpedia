-- Prove2me | Theorems.Thm_ImpulseNMFG_Verification_step_2
-- name    : ImpulseNMFG.Verification.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:27.922191+00:00
-- url     : https://prove2.me/theorems/f47232a0-68b3-4fe2-b501-d02dea82f7da
-- title:
--   Theorem 2.12, proof, Step 2, p. 12 — candidate payoff equals value
-- statement:
--   Suppose the candidate profile $\varphi^*$ is admissible at $x\in S$. For every player $i$ and every admissible realization of that profile,
--   $$
--   V_i(x)=J^i(x;\varphi^*).
--   $$
--   Under the candidate profile, the comparisons used for deviations become equalities. Combined with Step 1, this identifies the equilibrium costs.
--
--   **Formalization Note** The assertion ranges over every admissible realization; the admissibility hypothesis itself asks only for the existence of one. The candidate action regions are constructed from $V$ and $\xi$. The hypothesis that $\partial D_i$ is negligible (the time $X$ spends on $\partial D_i$ has Lebesgue measure zero along every admissible deviation) is added to the page. It is the occupation-time hypothesis of Øksendal's Theorem 10.4.1, whose proof the paper cites for its approximation step; without it the statement fails for degenerate $\sigma$, because a path can run along $\partial D_i$, where (2.13d) constrains nothing.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, p. 12, Theorem 2.12, proof, Step 2

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State IsBrownianBasis)

namespace ImpulseNMFG.Verification
noncomputable section
/-- Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls,
arXiv:1901.08085v4, p. 12, Theorem 2.12, proof, Step 2.
The candidate profile has cost V_i(x) on every admissible realization.
Formalization Note: `hocc` (the time X spends on ∂D_i is Lebesgue-null along every admissible
deviation) is added to the page's hypotheses. It is the occupation-time hypothesis of
Øksendal's Theorem 10.4.1, whose proof the paper cites for (a)–(c); without it the statement
fails for degenerate σ (a path running along ∂D_i, where (2.13d) imposes nothing on f_i). -/
theorem step_2 {N d M : ℕ} [NeZero N] {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin M → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game N d M) (hG : G.Standing)
    (V : Fin N → State d → ℝ) (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i)
    (hii : ∀ i, Regular G V ξ i)
    (hiii : ∀ i, BoundaryRegular G V ξ i)
    (x : State d) (hx : x ∈ G.S)
    (hocc : ∀ i, BoundaryNegligible P 𝔽 W G V ξ x i)
    (hadm : InPhi P 𝔽 W G x (starProfile G V ξ)) :
    ∀ (i : Fin N) (Y : ℕ → ℝ≥0 → Ω → State d),
      IsAdmissible P 𝔽 W G x (starProfile G V ξ) Y →
      V i x = cost P G x (starProfile G V ξ) Y i := by sorry
end
end ImpulseNMFG.Verification

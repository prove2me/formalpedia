-- Prove2me | Theorems.Thm_ImpulseNMFG_Verification_step_1
-- name    : ImpulseNMFG.Verification.step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:32.037316+00:00
-- url     : https://prove2.me/theorems/b89ef929-79eb-406e-876e-a286ff0f6339
-- title:
--   Theorem 2.12, proof, Step 1, pp. 10–12 — deviation cost bounds candidate value
-- statement:
--   Fix a player $i$ and let that player replace the candidate strategy by any strategy whose full profile is admissible at $x\in S$. For every admissible realization $Y$ of the deviating profile,
--   $$
--   V_i(x)\le J^i\bigl(x;(\varphi^{*,-i},\varphi_i)\bigr).
--   $$
--   Thus $V_i(x)$ is a lower bound on the cost of every admissible unilateral deviation. This is the comparison half of the Nash verification.
--
--   **Formalization Note** The comparison ranges over all admissible realizations of every admissible deviation. The candidate profile itself need not be assumed admissible for this step. Costs are minimized, so the inequality points toward the deviating cost. The hypothesis that $\partial D_i$ is negligible (the time $X$ spends on $\partial D_i$ has Lebesgue measure zero along every admissible deviation) is added to the page. It is the occupation-time hypothesis of Øksendal's Theorem 10.4.1, whose proof the paper cites for its approximation step; without it the statement fails for degenerate $\sigma$, because a path can run along $\partial D_i$, where (2.13d) constrains nothing.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, pp. 10–12, Theorem 2.12, proof, Step 1

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
arXiv:1901.08085v4, pp. 10–12, Theorem 2.12, proof, Step 1.
Every admissible unilateral deviation has cost at least V_i(x). The model uses the
published Itô SolvesFrom and the pathwise N-player realization.
Formalization Note: `hocc` (the time X spends on ∂D_i is Lebesgue-null along every admissible
deviation) is added to the page's hypotheses. It is the occupation-time hypothesis of
Øksendal's Theorem 10.4.1, whose proof the paper cites for (a)–(c); without it the statement
fails for degenerate σ (a path running along ∂D_i, where (2.13d) imposes nothing on f_i). -/
theorem step_1 {N d M : ℕ} [NeZero N] {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin M → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game N d M) (hG : G.Standing)
    (V : Fin N → State d → ℝ) (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i)
    (hii : ∀ i, Regular G V ξ i)
    (hiii : ∀ i, BoundaryRegular G V ξ i)
    (x : State d) (hx : x ∈ G.S)
    (hocc : ∀ i, BoundaryNegligible P 𝔽 W G V ξ x i) :
    ∀ (i : Fin N) (A : Set (State d)) (ξ' : State d → G.Imp i)
      (Y : ℕ → ℝ≥0 → Ω → State d),
      IsAdmissible P 𝔽 W G x ((starProfile G V ξ).update i A ξ') Y →
      V i x ≤ cost P G x ((starProfile G V ξ).update i A ξ') Y i := by sorry
end
end ImpulseNMFG.Verification

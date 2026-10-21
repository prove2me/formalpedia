-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_lemma_5
-- name    : FutileDynamics.StaticOpt.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:43.53923+00:00
-- url     : https://prove2.me/theorems/27b5b6d6-f21d-405e-bbad-b395bce1b8fb
-- title:
--   Lemma 5, p. ec 6 — for S ∈ S×1, S×T is incentive compatible and PrincipalUtility(S×T, σTR, F, T) = T·PrincipalUtility(S, σTR, F, 1)
-- statement:
--   Let $S\in\mathcal S^{\times1}$ be a single-round direct IC/IR mechanism and $S^{\times T}$ its repetition over $T$ rounds. Then $S^{\times T}$ is incentive compatible, and for every distribution $F$
--   $$\mathrm{PrincipalUtility}(S^{\times T},\sigma^{TR},F,T)=T\cdot\mathrm{PrincipalUtility}(S,\sigma^{TR},F,1),$$
--   with $\sigma^{TR}$ the truthful strategy (CONTINUE, then report each shock).
--
--   Direct static mechanisms are therefore admissible in the multi-round problem, and their value scales linearly in $T$.
--
--   **Formalization Note** IC at horizon $T$ is the full notion: every distribution and every feasible, history-dependent and randomized deviation. Assumed: $0<T$, $\Theta$ standard Borel and nonempty, and the model conventions.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. ec 6, Lemma 5

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Lemma 5** (p. ec 6): for any `S ∈ S^{×1}`, `S^{×T}` is incentive compatible and
`PrincipalUtility(S^{×T}, σ^TR, F, T) = T · PrincipalUtility(S, σ^TR, F, 1)` for every distribution `F`. -/
theorem lemma_5 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    ∀ d : DirectRule G, SingleRoundIC G d → IsIC G (repeatDirect G d) T ∧
      ∀ F : Measure Θ, IsProbabilityMeasure F →
        principalUtility G (repeatDirect G d) (repeatDirect G d).recom F T =
          T * principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1 := by sorry

end FutileDynamics.StaticOpt

-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_shapley_eq_sum_of_unanimity_expansion
-- name    : MonotonicSolutions.StrongMono.shapley_eq_sum_of_unanimity_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:08:29.688532+00:00
-- url     : https://prove2.me/theorems/2a69e936-e61b-4dea-8bb9-d4af39c6bbba
-- title:
--   Shapley value of a game in the form (9): $\mathrm{Sh}_i(v)=\sum_{R\ni i} c_R/|R|$
-- statement:
--   Let $v$ be a cooperative game on $N = \{1, \dots, n\}$ with $v(\emptyset) = 0$, written in the form (9) as
--   $$v = \sum_{\emptyset \ne R \subseteq N} c_R\, v_R$$
--   with real coefficients $c_R$ and primitive games $v_R$. Then for every player $i$ the Shapley value of $i$ is
--   $$\mathrm{Sh}_i(v) = \sum_{R \subseteq N,\ i \in R} \frac{c_R}{|R|}.$$
--
--   This identifies the target of the uniqueness proof of Theorem 2: each primitive game $c_R v_R$ is split equally among the members of $R$.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, proof of Theorem 2 ("The Shapley value can be expressed as …")

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 70, proof of Theorem 2): on a game written in the form (9),
`v = ∑_{∅ ≠ R ⊆ N} c_R v_R`, the Shapley value is `Sh_i(v) = ∑_{R : i ∈ R} c_R / |R|`. -/
theorem shapley_eq_sum_of_unanimity_expansion {n : ℕ} (v : Game n)
    (c : Finset (Fin n) → ℝ)
    (hv : ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S)
    (i : Fin n) :
    Supermodularity.Cooperative.ShapleyValue v.1 i =
      ∑ R ∈ Finset.univ.powerset.filter (fun R => i ∈ R), c R / R.card := by sorry

end MonotonicSolutions.StrongMono

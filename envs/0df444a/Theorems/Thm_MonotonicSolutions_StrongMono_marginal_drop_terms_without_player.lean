-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_marginal_drop_terms_without_player
-- name    : MonotonicSolutions.StrongMono.marginal_drop_terms_without_player
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:10:08.350727+00:00
-- url     : https://prove2.me/theorems/dc2565ff-b51a-47f5-8620-878ffec21c0c
-- title:
--   Proof of Theorem 2 — dropping the terms $R \not\ni i$ from (9) leaves $v^i$ unchanged
-- statement:
--   Let $N = \{1, \dots, n\}$, let $(c_R)_{R \subseteq N}$ be real coefficients and $i \in N$ a player. Consider the two set functions
--   $$v = \sum_{\emptyset \ne R \subseteq N} c_R\, v_R, \qquad w = \sum_{R \subseteq N,\ i \in R} c_R\, v_R,$$
--   where $v_R$ is the primitive game ($v_R(S) = 1$ if $R \subseteq S$, else $0$). Then the marginal contributions of $i$ agree:
--   $$w^i(S) = v^i(S) \quad \text{for every } S \subseteq N.$$
--
--   In the inductive step of Theorem 2 this identity, combined with (7) and the induction hypothesis applied to the shorter expression $w$, gives Eq. (10): $\varphi_i(v) = \varphi_i(w) = \sum_{R \ni i} c_R/|R|$ for every player $i$ outside the common intersection of the coalitions in the expression.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70–71, proof of Theorem 2 ("w^i(S) = v^i(S) for all S", leading to Eq. (10))

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71, proof of Theorem 2): if `v = ∑_{∅ ≠ R ⊆ N} c_R v_R` and
`w = ∑_{R : i ∈ R} c_R v_R` keeps only the terms whose coalition contains `i`, then
`w^i(S) = v^i(S)` for every coalition `S`. -/
theorem marginal_drop_terms_without_player {n : ℕ} (c : Finset (Fin n) → ℝ) (i : Fin n)
    (S : Finset (Fin n)) :
    marginal (fun T => ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty ∧ i ∈ R),
        c R * unanimity R T) i S =
      marginal (fun T => ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R T) i S := by sorry

end MonotonicSolutions.StrongMono

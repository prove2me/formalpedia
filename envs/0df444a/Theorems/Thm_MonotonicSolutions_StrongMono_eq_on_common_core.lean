-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_eq_on_common_core
-- name    : MonotonicSolutions.StrongMono.eq_on_common_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:10:56.838021+00:00
-- url     : https://prove2.me/theorems/f400af41-edcb-4450-9afa-06069f29818c
-- title:
--   Proof of Theorem 2 — symmetry equalizes the players of $\bigcap_k R_k$
-- statement:
--   Let $\varphi$ be a symmetric map from games on $N = \{1, \dots, n\}$ to $\mathbb{R}^N$, and let $v$ be a game written as
--   $$v = \sum_{\emptyset \ne R \subseteq N} c_R\, v_R .$$
--   Suppose players $i$ and $j$ both belong to every nonempty coalition $R$ with $c_R \ne 0$, i.e. to the intersection $\bigcap_k R_k$ of the coalitions that actually occur in the expression. Then
--   $$\varphi_i(v) = \varphi_j(v).$$
--
--   This is the symmetry step that closes the induction in the proof of Theorem 2: all members of the common intersection receive the same amount, and efficiency then pins that amount down.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 71, proof of Theorem 2 ("By symmetry, φ_i(v) is a constant c for all members of R")

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71, proof of Theorem 2): let `φ` be symmetric and
`v = ∑_{∅ ≠ R ⊆ N} c_R v_R`. If players `i` and `j` both belong to every coalition `R ≠ ∅`
with `c_R ≠ 0` (i.e. to the common core `∩_k R_k` of the expression), then
`φ_i(v) = φ_j(v)`. -/
theorem eq_on_common_core {n : ℕ} (φ : Game n → Fin n → ℝ) (hS : IsSymmetric φ)
    (v : Game n) (c : Finset (Fin n) → ℝ)
    (hv : ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S)
    (i j : Fin n) (hij : ∀ R : Finset (Fin n), R.Nonempty → c R ≠ 0 → i ∈ R ∧ j ∈ R) :
    φ v i = φ v j := by sorry

end MonotonicSolutions.StrongMono

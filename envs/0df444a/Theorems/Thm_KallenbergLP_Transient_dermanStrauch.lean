-- Prove2me | Theorems.Thm_KallenbergLP_Transient_dermanStrauch
-- name    : KallenbergLP.Transient.dermanStrauch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:38:42.39003+00:00
-- url     : https://prove2.me/theorems/8878bb33-6cd9-4261-81ee-aa9d6f96e130
-- title:
--   Theorem 2.5.1 — memoryless reproduction of mixed occupancies
-- statement:
--   Fix an initial distribution $\beta$ on $E$, policies $R_1,R_2,\ldots$, and nonnegative weights $w_k$ summing to one. There is a memoryless policy $Q$ such that, for every epoch $t$, state $j$, and admissible action $a\in A(j)$,
--
--   $$\sum_i\beta_i P_Q(X_t=j,Y_t=a\mid X_1=i)=\sum_i\beta_i\sum_{k\ge1}w_kP_{R_k}(X_t=j,Y_t=a\mid X_1=i).$$
--
--   The result lets a time-dependent Markov policy reproduce the one-period state-action frequencies of a mixture of arbitrary history-dependent policies.
--
--   **Formalization Note** Natural-number index $k=0$ in Lean corresponds to $k=1$ in the book.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 32, Theorem 2.5.1, equation (2.5.1)

import Definitions.Def_KallenbergLP_Transient_Criteria
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 2.5.1: a memoryless policy reproduces a mixture's one-period occupancies. -/
theorem dermanStrauch
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ₁ : (∑ i : Fin N, β i) = 1)
    (R : ℕ → Policy M) (w : ℕ → ℝ)
    (hw₀ : ∀ k, 0 ≤ w k) (hw₁ : HasSum w 1) :
    ∃ Q : Policy M, Memoryless M Q ∧
      ∀ (t : ℕ) (j : Fin N) (a : α), a ∈ M.actions j →
        (∑ i : Fin N, β i * occupancy M Q i j a t) =
          ∑' k : ℕ, w k *
            (∑ i : Fin N, β i * occupancy M (R k) i j a t) := by sorry

end KallenbergLP.Transient

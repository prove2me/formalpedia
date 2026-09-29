-- Prove2me | Theorems.Thm_FoundationsML_ReinforcementLearning_value_iteration_converges
-- name    : FoundationsML.ReinforcementLearning.value_iteration_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:39:05.518138+00:00
-- url     : https://prove2.me/theorems/da94f611-6dda-4b77-9e06-7aebda7c9268
-- title:
--   Theorem 17.11 — Value iteration converges
-- statement:
--   **Statement (Theorem 17.11, p. 388, PDF p. 405).** For any initial value $V_0$, the sequence
--   defined by $V_{n+1}=\Phi(V_n)$ converges to $V^*$, where $\Phi$ is the Bellman optimality
--   operator (17.8) and $V^*$ is the optimal value function (a fixed point of $\Phi$, by (17.4)).
--   The proof shows $\Phi$ is $\gamma$-Lipschitz for $\lVert\cdot\rVert_\infty$ on $\mathbb
--   R^{|S|}$ (a contraction, since $\gamma<1$), then invokes the Banach fixed-point property of
--   the complete, finite-dimensional metric space $\mathbb R^{|S|}$.
--
--   This is the correctness guarantee for the value iteration algorithm (figure 17.4): starting
--   from an arbitrary value vector and repeatedly applying $\Phi$ converges to the true optimal
--   value function, regardless of the starting point.
--
--   **Formalization Note.** `Vstar` and the hypothesis `hVstar : Φ(Vstar) = Vstar` record that
--   $V^*$ is a fixed point of $\Phi$; existence and uniqueness of this fixed point (Theorem
--   17.8/eq. (17.4)) are outside this chunk's scope (§17.2–17.4.2), so they are recorded as an
--   explicit, disclosed hypothesis rather than re-derived — the theorem's own genuine content,
--   the contraction argument driving convergence of the iterates to *any* given fixed point, is
--   exactly what is asserted. `(BellmanOperator hA P Er γ)^[n] V0` is `Φ` iterated `n` times from
--   `V0`, matching $V_{n+1}=\Phi(V_n)$ with $V_0$ as given; convergence is stated in the sup norm
--   on `S → ℝ` (the canonical norm on a `Fintype`-indexed product, matching $\lVert\cdot
--   \rVert_\infty$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 388, Theorem 17.11 (PDF p. 405)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_BellmanOperator

namespace FoundationsML.ReinforcementLearning

/-- Theorem 17.11 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 388, PDF p. 405). For any initial value `V0`, the sequence defined by
`V_{n+1} = Φ(V_n)` converges to `V*`, where `Φ` is the Bellman optimality operator (17.8) and
`V*` is a fixed point of `Φ` (the optimal value function, by (17.4)). The book's proof shows `Φ`
is `γ`-Lipschitz (a contraction, since `γ < 1`) for `‖·‖∞` on `ℝ^{|S|}`, then invokes the Banach
fixed-point property of the complete, finite-dimensional metric space `ℝ^{|S|}`.

**Formalization Note.** `Vstar` and the hypothesis `hVstar : Φ(Vstar) = Vstar` record that `V*`
is a fixed point of `Φ` — existence and uniqueness of this fixed point (Theorem 17.8/eq. (17.4))
are outside this chunk's scope (§17.2–17.4.2 stops short of re-deriving optimal-policy
existence); the theorem's own genuine content, the contraction argument driving convergence of
the iterates to *any* given fixed point, is exactly what is asserted here.
`(BellmanOperator hA P Er γ)^[n] V0` is `Φ` iterated `n` times from `V0` (`Function.iterate`),
matching `V_{n+1} = Φ(V_n)` with `V_0` as given. Convergence is `Filter.Tendsto` to `nhds Vstar`
in the space `S → ℝ`, whose canonical `Fintype`-indexed product norm is the sup norm `‖·‖∞`
the book's proof uses. -/
theorem value_iteration_converges {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (hA : (Finset.univ : Finset A).Nonempty)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (Vstar : S → ℝ) (hVstar : BellmanOperator hA P Er γ Vstar = Vstar)
    (V0 : S → ℝ) :
    Filter.Tendsto (fun n : ℕ => (BellmanOperator hA P Er γ)^[n] V0) Filter.atTop
      (nhds Vstar) := by sorry

end FoundationsML.ReinforcementLearning

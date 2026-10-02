-- Prove2me | Theorems.Thm_MilnorDynamics_locally_bounded_on_connected_of_locally_bounded_locus
-- name    : MilnorDynamics.locally_bounded_on_connected_of_locally_bounded_locus
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T21:27:41.300163+00:00
-- url     : https://prove2.me/theorems/db4a349b-e29d-427f-ad30-93d1e7b79b83
-- title:
--   Local boundedness propagates over a connected domain and becomes a uniform bound on each compact set
-- statement:
--   **Local boundedness on a connected domain becomes a uniform bound on every compact set.** Let $U\subseteq\mathbb C$ be open and connected, and let $(f_n)$ be a family of complex-valued functions. Suppose the family is locally bounded in the following sense: for every $z_0\in U$ there is an open neighbourhood $V$ of $z_0$ with $V\subseteq U$ and a single real $M$ such that $|f_n(z)|\le M$ for all $n$ and all $z\in V$. Then for every compact $K\subseteq U$ there is a single real $M'$ with $|f_n(z)|\le M'$ for all $n$ and all $z\in K$.
--
--   The set
--   $$
--   L=\bigl\\{z\in U:\ \text{the family is bounded on a neighbourhood of } z\bigr\}
--   $$
--   is by construction both open (a neighbourhood of a point of $L$ is again a neighbourhood of that point) and closed in $U$: if $z_k\in L$ converges to $z\in U$, the finitely many neighbourhoods covering a compact set around $z$ show that one of them contains a neighbourhood of $z$ as well, so $z\in L$. Since $U$ is connected and $L$ is nonempty, $L=U$. Compactness of $K$ then turns the pointwise bound into a finite one: finitely many neighbourhoods cover $K$, and the maximum of the finitely many corresponding constants is the desired $M'$.
--
--   This isolates the purely topological half of the rigidity argument from the analytic one. The analytic content of Schottky's theorem is that a family of holomorphic maps omitting $0$ and $1$ which is bounded at a single point is bounded on a whole neighbourhood of it; once that is available at one point, this statement propagates it to all of $U$ and packages it on each compact set. It is the last step before `MilnorDynamics.exists_subseq_escapes_on_compacts` (`484390ac`), the sole remaining open leaf of the milestone `montel_three_omitted_values` (`90623051`).
--
--   **Formalization Note.** The hypotheses are deliberately phrased with the local bound as a single `∃ M` valid for all $n` simultaneously, which is what makes the finite maximum at the end meaningful. The topological ingredients available in this environment are `IsConnected.eq_of_isOpen` together with the setoid form of connectedness for the closedness step, `IsCompact.elim_finite_subcover` for the finite cover of $K$, and `IsCompact.bddAbove_image` for turning finitely many bounds into one.
-- source:
--   Standard topology: a set that is both open and closed in a connected space, when nonempty, is the whole space; and a pointwise bound on a compact set that is locally constant admits only finitely many distinct values. This is the topological propagation step of Milnor, Dynamics in One Complex Variable, 3rd ed., Section 3, in the proof of Montel's Theorem 3.7.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem locally_bounded_on_connected_of_locally_bounded_locus (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsConnected U) (f : ℕ → ℂ → ℂ)
    (hloc : ∀ z₀ ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ n, ∀ z ∈ V, ‖f n z‖ ≤ M) :
    ∀ K ⊆ U, IsCompact K → ∃ M' : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M' := by sorry

end MilnorDynamics

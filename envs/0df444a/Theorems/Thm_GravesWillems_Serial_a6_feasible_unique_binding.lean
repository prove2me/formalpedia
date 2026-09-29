-- Prove2me | Theorems.Thm_GravesWillems_Serial_a6_feasible_unique_binding
-- name    : GravesWillems.Serial.a6_feasible_unique_binding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:19:01.700012+00:00
-- url     : https://prove2.me/theorems/a0b08105-28e3-4273-95ff-7c5ac6a9f1da
-- title:
--   Proof of the Result — (A6) is feasible and is the unique binding solution of (A3)
-- statement:
--   Let $T_1, \dots, T_N \in \mathbb{N}$ be lead times and $D : \mathbb{N} \to \mathbb{R}$ a nondecreasing demand bound with $D(0) = 0$. Let $B^{(A6)}$ be the vector
--   $$B_1 = D(T_1), \qquad B_i = D(T_1 + \dots + T_i) - D(T_1 + \dots + T_{i-1}), \quad i = 2, \dots, N.$$
--   Then:
--   1. $B^{(A6)}$ is feasible for $\mathbf P^*$: it is nonnegative and satisfies (A3);
--   2. every constraint of (A3) holds with equality: $B_1 + \dots + B_i = D(T_1 + \dots + T_i)$ for $i = 1, \dots, N$;
--   3. it is the unique binding solution: any real vector $B$ with $B_1 + \dots + B_i = D(T_1 + \dots + T_i)$ for all $i = 1, \dots, N$ agrees with $B^{(A6)}$ on stages $1, \dots, N$.
--
--   This settles the feasibility half of the Result and identifies the endpoint of the improvement argument of its proof.
--
--   **Formalization Note** The paper's Result assumes $D$ nondecreasing; $D(0) = 0$ is the paper's convention (§2, p. 70: "We define $D_j(0) = 0$"; in the appendix $D(\tau)$ is the maximum demand over $\tau$ periods). Without it $B_1 = D(T_1)$ may be negative (e.g. $D \equiv -1$).
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, pp. 81-82, Appendix, proof of the Result (first sentence, p. 81; uniqueness of the binding solution, p. 82)

import Mathlib
import Definitions.Def_GravesWillems_Serial_programP

namespace GravesWillems.Serial

/-- Appendix, proof of the Result (Graves–Willems 2000, pp. 81–82): if `D(0) = 0` and `D` is
nondecreasing, the vector (A6) is nonnegative and satisfies every constraint (A3) with equality,
hence is feasible for `P*`; and every base-stock vector satisfying all constraints (A3) with
equality coincides with (A6) on stages `1, …, N`. -/
theorem a6_feasible_unique_binding (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ)
    (hD0 : D 0 = 0) (hD : Monotone D) :
    Feasible N T D (a6 N T D) ∧
    (∀ i ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 i, a6 N T D m = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ B : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m)) →
      ∀ i ∈ Finset.Icc 1 N, B i = a6 N T D i := by sorry

end GravesWillems.Serial

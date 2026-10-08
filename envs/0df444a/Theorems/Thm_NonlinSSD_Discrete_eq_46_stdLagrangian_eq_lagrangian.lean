-- Prove2me | Theorems.Thm_NonlinSSD_Discrete_eq_46_stdLagrangian_eq_lagrangian
-- name    : NonlinSSD.Discrete.eq_46_stdLagrangian_eq_lagrangian
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:03:08.424485+00:00
-- url     : https://prove2.me/theorems/e62d7eda-062f-4be3-be49-cac223683594
-- title:
--   Eq. (46) — the multipliers μ generate a utility u_i, and the standard Lagrangian Λ equals the Lagrangian (42)
-- statement:
--   Fix the data of problem (38)–(41) and any real numbers $\mu_{ik}$, $i \in I$, $k \in J$. Define
--   $$u_i(t) = -\sum_{k=1}^n \mu_{ik}(y_{ik} - t)_+ . \tag{46}$$
--   Then for every $i$ and every $X$,
--   $$\sum_{k=1}^n \mu_{ik} \sum_{j=1}^n p_j (y_{ik} - x_{ij})_+ = -\sum_{j=1}^n p_j\, u_i(x_{ij}),$$
--   and consequently, for all $z$, $X$ and $\theta$,
--   $$\Lambda(z, X, \mu, \theta) = L(z, X, u, \theta),$$
--   where $\Lambda$ is the standard Lagrangian of (38)–(41) with multipliers $\mu$ for the dominance constraints (39), and $L$ is the Lagrangian (42).
--
--   This identity is how the proof of Theorem 6 converts the classical Kuhn–Tucker multipliers of the dominance constraints into a utility function.
--
--   **Formalization Note.** No sign condition on $\mu$ and no condition on $p$ are needed for this algebraic identity, so none is assumed.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 17, Eq. (46), proof of Theorem 6

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

namespace NonlinSSD.Discrete

theorem eq_46_stdLagrangian_eq_lagrangian {m n N : ℕ} (p : Fin n → ℝ)
    (h : Fin n → (Fin N → ℝ) → ℝ) (g : Fin m → Fin n → (Fin N → ℝ) → ℝ)
    (y : Fin m → Fin n → ℝ) (μ : Fin m → Fin n → ℝ) :
    (∀ (i : Fin m) (X : Fin m → Fin n → ℝ),
      ∑ k, μ i k * ∑ j, p j * max (y i k - X i j) 0 =
        -∑ j, p j * multiplierUtility (y i) (μ i) (X i j)) ∧
    (∀ (z : Fin N → ℝ) (X θ : Fin m → Fin n → ℝ),
      stdLagrangian p h g y z X μ θ =
        lagrangian p h g y z X (fun i => multiplierUtility (y i) (μ i)) θ) := by sorry

end NonlinSSD.Discrete

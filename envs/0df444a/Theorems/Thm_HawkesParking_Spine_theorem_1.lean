-- Prove2me | Theorems.Thm_HawkesParking_Spine_theorem_1
-- name    : HawkesParking.Spine.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:28.977741+00:00
-- url     : https://prove2.me/theorems/0006ac55-c777-4895-aed9-16e8ff61a0d3
-- title:
--   Theorem 1, pp. 12–13 — given $N=k+1$, the compensator points have the law of $\rho$ times the order statistics of $\pi-U$, $\pi$ a uniform parking function
-- statement:
--   Let $g$ be an excitation kernel satisfying the standing assumptions, with $\rho=\int_0^\infty g\in(0,1)$, and let $k\in\mathbb N$. Given that the Hawkes cluster consists of $N=k+1$ events, the compensator-transformed arrival epochs $\Lambda_1,\dots,\Lambda_k$ satisfy
--   $$(\Lambda_1,\dots,\Lambda_k)\ \overset{D}{=}\ \rho\cdot\big((\pi-U)_{(1)},\dots,(\pi-U)_{(k)}\big),$$
--   where $(\pi-U)_{(1)}<\dots<(\pi-U)_{(k)}$ are the order statistics of $\pi-U$, $\pi\in\mathsf{PF}_k$ is a parking function of length $k$ drawn uniformly at random, and $U\in(0,1)^k$ has i.i.d. standard uniform coordinates independent of $\pi$.
--
--   A uniformly random parking function is thus a hidden "spine" of the Hawkes cluster: it determines which unit cell of the Dyck decomposition each compensator point falls in, and independent uniforms fill in the rest.
--
--   **Formalization Note.** (1) The paper writes eq. (8) coordinatewise, $\Lambda_i\overset{D}{=}\rho\,(\pi-U)_{(i)}$; its proof (p. 16) and abstract establish the equality of the joint laws, which is stated here and implies (8). (2) The left side is the conditional law of the compensator points given $N=k+1$, built from the likelihood-defined cluster law (see the Model item); the right side is the law of $\rho\cdot\mathrm{sort}(\pi-U)$, written as the uniform mixture over $\pi\in\mathsf{PF}_k$. (3) $k=0$ is allowed, as on the page ("Let $k\in\mathbb N$"); both sides are then the point mass on the empty vector. (4) Added hypotheses, as for every cluster statement: $g$ measurable and $\rho>0$.
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, pp. 12–13, Theorem 1, eq. (8)

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
theorem theorem_1 (g : ℝ → ℝ) (hg : IsKernel g) (k : ℕ) :
    condCompensatorLaw g k = spineLaw (rho g) k := by sorry
end HawkesParking.Spine

-- Prove2me | Theorems.Thm_HighDimProb_RandomMatrices_quadratic_form_on_net
-- name    : HighDimProb.RandomMatrices.quadratic_form_on_net
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:23:21.29099+00:00
-- url     : https://prove2.me/theorems/66e14664-6067-4d0b-b3c2-4958d11db063
-- title:
--   Exercise 4.4.3(a) — Quadratic form on a net
-- statement:
--   This is **Exercise 4.4.3(a)**: the reduction of the operator norm to a supremum over a pair
--   of finite nets, which the goal theorem's proof invokes directly ("By Exercise 4.4.3, the
--   operator norm of $A$ can be bounded using these nets") to turn the union bound over the
--   (infinite) unit spheres into a union bound over finite sets.
--
--   Let $A$ be an $m \times n$ matrix and $\varepsilon \in [0, 1/2)$. For any ε-net $N$ of the
--   sphere $S^{n-1} \subset \mathbb R^n$ and any ε-net $M$ of the sphere
--   $S^{m-1} \subset \mathbb R^m$ (companion definition `IsEpsNet`),
--
--   $$
--   \sup_{x \in N,\, y \in M} \langle Ax, y\rangle \;\le\; \|A\| \;\le\;
--     \frac{1}{1 - 2\varepsilon}\, \sup_{x \in N,\, y \in M} \langle Ax, y\rangle,
--   $$
--
--   where $\|A\|$ is the operator norm (companion definition `matrixOpNorm`) and
--   $\langle \cdot,\cdot\rangle$ is the Euclidean inner product.
--
--   **Formalization Note** $m, n$ are required positive so that the unit spheres $S^{n-1}$,
--   $S^{m-1}$ are nonempty, which (together with the ε-net hypotheses) makes $N$ and $M$
--   nonempty and the supremum on the right a supremum of a nonempty, bounded set — avoiding the
--   real `sSup`/`sInf` junk-value convention (Mathlib's `sSup ∅ = 0`) from silently altering the
--   statement's content. $\langle Ax, y \rangle$ is `inner ℝ (Matrix.toEuclideanLin A x) y`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Exercise 4.4.3(a), p. 90 (PDF p. 98)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

namespace HighDimProb.RandomMatrices

/-- **Exercise 4.4.3(a)** (Quadratic form on a net), Vershynin, *High-Dimensional Probability*
(2018), p. 90.

Let `A` be an `m × n` matrix and `ε ∈ [0, 1/2)`. Then for any `ε`-net `N` of the sphere
`Sⁿ⁻¹` and any `ε`-net `M` of the sphere `Sᵐ⁻¹`,
`sup_{x ∈ N, y ∈ M} ⟨Ax, y⟩ ≤ ‖A‖ ≤ (1/(1-2ε)) sup_{x ∈ N, y ∈ M} ⟨Ax, y⟩`. -/
theorem quadratic_form_on_net {m n : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (N : Set (EuclideanSpace ℝ (Fin n)))
    (hN : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) N ε)
    (M : Set (EuclideanSpace ℝ (Fin m)))
    (hM : IsEpsNet (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) M ε) :
    sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M)
        ≤ matrixOpNorm A ∧
    matrixOpNorm A ≤ (1 / (1 - 2 * ε)) *
        sSup (Set.image2 (fun x y => inner ℝ (Matrix.toEuclideanLin A x) y) N M) := by sorry

end HighDimProb.RandomMatrices

-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_psh_iff_complexHessian_posSemidef
-- name    : LeblSCV.Pseudoconvex.psh_iff_complexHessian_posSemidef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:20:44.20835+00:00
-- url     : https://prove2.me/theorems/1d4cfea4-c8d3-4329-a6b3-c7b02e26867c
-- title:
--   Proposition 2.4.9 — $C^2$ plurisubharmonic iff complex Hessian positive semidefinite
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and $f : U \to \mathbb{R}$ be $C^2$-smooth. Then $f$ is plurisubharmonic if and only if the complex Hessian matrix
--   $$\left[ \frac{\partial^2 f}{\partial \bar z_k \partial z_\ell} \right]_{k\ell}$$
--   is positive semidefinite at every point of $U$.
--
--   This is the infinitesimal test for plurisubharmonicity. It is also the bridge to the Levi form: Theorem 2.5.8 uses it to compare Hartogs and Levi pseudoconvexity.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. $C^2$ is `ContDiffOn ℝ 2 f U`. Positive semidefinite is Mathlib's `Matrix.PosSemidef` for complex matrices (Hermitian, with $\bar c^{T} H c \geq 0$ for every $c \in \mathbb{C}^n$), under the partial order on $\mathbb{C}$ from `open ComplexOrder`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 85, Proposition 2.4.9

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_complexHessian

open ComplexOrder

namespace LeblSCV.Pseudoconvex

/-- Proposition 2.4.9 (Lebl, p. 85). Let `U ⊂ ℂⁿ` be open. A `C²`-smooth `f : U → ℝ` is
plurisubharmonic iff the complex Hessian matrix `[∂²f/∂z̄_k∂z_ℓ]_{kℓ}` is positive
semidefinite at every point of `U`. -/
theorem psh_iff_complexHessian_posSemidef {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hU : IsOpen U) (f : EuclideanSpace ℂ (Fin n) → ℝ) (hf : ContDiffOn ℝ 2 f U) :
    IsPlurisubharmonicOn (fun z => (f z : EReal)) U ↔
      ∀ p ∈ U, (complexHessian f p).PosSemidef := by sorry

end LeblSCV.Pseudoconvex

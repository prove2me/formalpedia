-- Prove2me | Theorems.Thm_GomoryGroup_Rel_basic_part_nonneg
-- name    : GomoryGroup.Rel.basic_part_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:29:58.26128+00:00
-- url     : https://prove2.me/theorems/18a350ab-4e6c-465a-8a07-e91faaa3db1d
-- title:
--   proof of THEOREM 1, p. 264 — ‖Ny‖ ≤ (D − 1)l, and for b ∈ K^B(l(D − 1)), b − Ny ∈ K^B so x_B ≥ 0
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $N$ an integer $m\times n$ matrix, $D=|\det B|$, $l=\max_{i=m+1,\dots,m+n}\|\alpha_i\|$ (Euclidean norm), and let $b\in\mathbb Z^m$ lie in the reduced cone $K^B(l(D-1))$. Then for every $y\in\mathbb N^n$ with $\sum_{i=1}^n y_i\le D-1$:
--
--   1. $\|Ny\|\le(D-1)l$;
--   2. $b-Ny\in K^B$, that is,
--   $$x_B=B^{-1}(b-Ny)\ge0 .$$
--
--   Combined with the LEMMA, this is the step that makes the basic part of the extended group solution nonnegative, and closes the proof of THEOREM 1.
--
--   **Formalization Note** $K^B(d)$ is the set of points whose closed Euclidean ball of radius $d$ lies in $K^B=\{\beta: B^{-1}\beta\ge0\}$. The norm is Euclidean, not Lean's default sup norm. $l=0$ when $n=0$.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 264, after THEOREM 4

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem basic_part_nonneg {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hB : B.det ≠ 0)
    (hb : (fun i => (b i : ℝ)) ∈ reducedCone B (ell N * ((detD B : ℝ) - 1))) :
    ∀ y : Fin n → ℕ, ∑ j, y j ≤ detD B - 1 →
      euclNorm (Nr N *ᵥ (fun j => (y j : ℝ))) ≤ ((detD B : ℝ) - 1) * ell N ∧
        0 ≤ (Br B)⁻¹ *ᵥ ((fun i => (b i : ℝ)) - Nr N *ᵥ (fun j => (y j : ℝ))) := by sorry

end GomoryGroup.Rel

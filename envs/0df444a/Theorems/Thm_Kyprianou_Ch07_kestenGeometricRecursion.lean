-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenGeometricRecursion
-- name    : Kyprianou.Ch07.kestenGeometricRecursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:16:24.254804+00:00
-- url     : https://prove2.me/theorems/768e28cd-2c33-4aa2-bd61-178bef29a564
-- title:
--   Kesten convolution-tail proof: uniform geometric bound from an affine recursion
-- statement:
--   If a real sequence xi satisfies xi(0) ≤ B and xi(n+1) ≤ A+(1+epsilon)xi(n) for positive epsilon, then xi(n)+A/epsilon ≤ (B+A/epsilon)(1+epsilon)^n. This is the deterministic induction step used after the convolution-tail splitting estimate in Kyprianou Lemma 7.14.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp. 201–202; original PDF pp. 210–211. The affine recursion for maximal tail ratios is iterated to derive the Kesten geometric estimate. Supports Chapter 7 published milestone 6402f145-487e-4df9-8af6-1ffe5610a800.

import Mathlib
set_option autoImplicit false
open Filter

theorem Kyprianou.Ch07.kestenGeometricRecursion
    (epsilon A B : Real)
    (hEpsilon : 0 < epsilon)
    (xi : Nat → Real)
    (hBase : xi 0 ≤ B)
    (hStep : ∀ n : Nat,
      xi (n + 1) ≤ A + (1 + epsilon) * xi n) :
    ∀ n : Nat,
      xi n + A / epsilon ≤
        (B + A / epsilon) * (1 + epsilon) ^ n := by
  sorry

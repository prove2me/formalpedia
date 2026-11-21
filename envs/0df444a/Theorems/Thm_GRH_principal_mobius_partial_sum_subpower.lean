-- Prove2me | Theorems.Thm_GRH_principal_mobius_partial_sum_subpower
-- name    : GRH.principal_mobius_partial_sum_subpower
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:30:07.411392+00:00
-- url     : https://prove2.me/theorems/9f5c3a9c-8069-4eb0-aab8-323a2d24c1e1
-- title:
--   Power-saving principal Möbius sums above the verified Dirichlet zero-free boundary
-- statement:
--   Let $q$ be a positive integer and let $\mu$ be the Möbius function. For every real $\sigma>0.8749570698$ one has
--   $$\sum_{\substack{1\le n\le N\\(n,q)=1}}\mu(n)=O_{q,\sigma}(N^\sigma).$$
--   This is the principal-character case of power-saving cancellation for sharp twisted Möbius sums. The exponent comes from the platform’s fixed zero-free region for Dirichlet $L$-functions.
-- source:
--   The zero-free input is https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918. The reciprocal estimates use https://prove2.me/theorems/4636708a-d1f1-4d25-8f1f-7b99460a4b70 and https://prove2.me/theorems/8d3b5652-26b7-4c3d-bbfb-ff27b997baa3. The sharp cutoff uses https://prove2.me/theorems/0cfc5f9d-8e47-4920-b235-f80b5f4f55a7. The pole removal and finite Euler product transfer use Mathlib’s DirichletContinuation.

import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Filter Asymptotics

theorem GRH.principal_mobius_partial_sum_subpower (q : ℕ) [NeZero q] (σ : ℝ) (hσ : (0.8749570698 : ℝ) < σ) :
    (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1),
      (1 : DirichletCharacter ℂ q) k * (ArithmeticFunction.moebius k : ℂ))
      =O[atTop] (fun N : ℕ ↦ (N : ℝ) ^ σ) := by sorry

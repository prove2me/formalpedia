-- Prove2me | Theorems.Thm_MasulloRH_finite_cutoff_cross_correlation
-- name    : MasulloRH.finite_cutoff_cross_correlation
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:21:22.606486+00:00
-- url     : https://prove2.me/theorems/f5a8e538-7087-4814-a19f-922bc9aad777
-- title:
--   Directed orbital cutoffs and their finite lag distribution
-- statement:
--   Let $a,b$ be finitely supported real sequences on $\mathbb Z$. Give lag $j$ the weight $c_{a,b}(j)=\sum_{k-i=j}a_i b_k$. For every real test sequence $f$, pairing $c_{a,b}$ against $f$ equals $\sum_{i,k}a_i b_k f(k-i)$. If $a,b$ are nonnegative and each has total mass one, $c_{a,b}$ also has these properties. Swapping the cutoffs reflects the lag: $c_{b,a}(j)=c_{a,b}(-j)$. In particular $c_{\delta_0,\delta_r}=\delta_r$ for every integer $r$.
-- source:
--   Finite cutoff calculation for Chapter 11 of Masullo, The Music of the Primes, §11.3.2, pp. 495–496, equations (11.3.2.3–5). Related upstream discussion: https://github.com/mccorvie/riemann-masullo/issues/1358.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

open Finset

theorem MasulloRH.finite_cutoff_cross_correlation :
    let corr (u v : ℤ →₀ ℝ) : ℤ →₀ ℝ :=
      ∑ i ∈ u.support, ∑ k ∈ v.support, Finsupp.single (k-i) (u i * v k)
    (∀ (a b : ℤ →₀ ℝ) (f : ℤ → ℝ),
      (∑ j ∈ (corr a b).support, corr a b j * f j) =
        ∑ i ∈ a.support, ∑ k ∈ b.support, (a i * b k) * f (k-i)) ∧
    (∀ a b : ℤ →₀ ℝ, (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      (∑ i ∈ a.support, a i) = 1 → (∑ i ∈ b.support, b i) = 1 →
      (∀ j, 0 ≤ corr a b j) ∧ (∑ j ∈ (corr a b).support, corr a b j) = 1) ∧
    (∀ (a b : ℤ →₀ ℝ) (j : ℤ), corr b a j = corr a b (-j)) ∧
    (∀ r : ℤ, corr (Finsupp.single 0 1) (Finsupp.single r 1) = Finsupp.single r 1) := by sorry

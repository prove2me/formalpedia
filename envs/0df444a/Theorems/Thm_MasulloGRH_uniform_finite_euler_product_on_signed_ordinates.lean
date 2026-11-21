-- Prove2me | Theorems.Thm_MasulloGRH_uniform_finite_euler_product_on_signed_ordinates
-- name    : MasulloGRH.uniform_finite_euler_product_on_signed_ordinates
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:01:34.066451+00:00
-- url     : https://prove2.me/theorems/a09f5fc7-520f-4b39-a866-734d8d92cce1
-- title:
--   Uniform lower bound for finite Euler products on corrected signed ordinates, across every real part
-- statement:
--   For any finite family of real numbers $q_j>1$, there is a constant $c>0$ depending only on that family. For every choice of unit phases $z_j$, there is a nondecreasing sequence $T_k\in[k,k+1]$ over all integers, escaping in both directions and satisfying $T_k\ge0$ for $k\ge0$ and $T_k\le0$ for $k<0$, such that for every $k$ and every real $\sigma$ the product $\prod_j|1-z_jq_j^{-(\sigma+iT_k)}|$ is at least $c$. This applies to unramified finite Hecke Euler factors by taking $q_j$ to be the prime ideal norms and $z_j$ the unramified character values. The strict negative index condition leaves $T_0$ free in $[0,1]$.
-- source:
--   Correction to Alessandro Maria Masullo, The Music of the Primes, 20 November 2026, Lemma 7.1.1.1 (7.1.1.3) and Proposition B.5.3.2 (B.5.3.3). Elementary finite sampling proof using the logarithms of the Euler norms.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Int
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open Finset Complex

theorem MasulloGRH.uniform_finite_euler_product_on_signed_ordinates {m : ℕ} (q : Fin m → ℝ) (hq : ∀ i, 1 < q i) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin m → ℂ, (∀ i, ‖z i‖ = 1) →
      ∃ T : ℤ → ℝ, (∀ k : ℤ, T k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧
        (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
        (∀ k, T k ≤ T (k+1)) ∧
        Filter.Tendsto (fun k => |T k|) Filter.cofinite Filter.atTop ∧
        ∀ k (σ : ℝ), c ≤ ∏ i, ‖1 - z i * (q i : ℂ) ^ (-((σ : ℂ) + (T k : ℂ) * Complex.I))‖ := by sorry

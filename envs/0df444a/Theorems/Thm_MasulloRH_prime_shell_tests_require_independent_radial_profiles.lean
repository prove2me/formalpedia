-- Prove2me | Theorems.Thm_MasulloRH_prime_shell_tests_require_independent_radial_profiles
-- name    : MasulloRH.prime_shell_tests_require_independent_radial_profiles
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:35:16.236274+00:00
-- url     : https://prove2.me/theorems/42029f23-a33d-4d01-be51-3dfcdfc3c503
-- title:
--   Smooth prime-shell tests force full rank and radial profile independence at common cutoffs
-- statement:
--   There are smooth, compactly supported real norm tests $f_q$ on $(1,\infty)$, one per prime $q$, for which $\sum_{k\in\mathbf Z}(p^{-k})^a f_q(p^{-k})$ is $p^a$ when $p=q$ and zero otherwise, for every real $a$. Choose any $N$ distinct rational primes $p_i$. If a common net of complex response matrices converges entrywise to $\log(p_i)\sum_k(p_i^{-k})^a f_{p_j}(p_i^{-k})$, eventually every factorization of the matrix has inner dimension at least $N$. If its entries at that cutoff have the radial integral form $\int W_i(t)V_j(t)\,d\mu(t)$ with integrable products, the shell functions $W_i$ are linearly independent over $\mathbf C$ modulo almost-everywhere equality for that measure. This covers the printed untwisted prime response in (11.3.2.1) and the real half weight $a=-1/2$. The conclusion is a necessary condition for any such prime-shell response calculation.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, frozen 20 November 2026, (11.3.1.4), (11.3.2.1–2) and (11.3.2.5); rational norm-invariant tests. Uses the distinction between the two local weights (mission comment 3248a5d4) and the double-Haar calculation db985081-fca8-4440-bfd1-276f6e60b4e6. New finite-test rank criterion.

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter MeasureTheory
open scoped Topology
open Set

theorem MasulloRH.prime_shell_tests_require_independent_radial_profiles :
    ∃ f : Nat.Primes → ℝ → ℝ,
      (∀ q, ContDiff ℝ (⊤ : ℕ∞) (f q) ∧ HasCompactSupport (f q) ∧ tsupport (f q) ⊆ Set.Ioi 1) ∧
      (∀ (p q : Nat.Primes) (a : ℝ), (∑' k : ℤ, (((p : ℝ)^(-k))^a) * f q ((p : ℝ)^(-k))) = if p = q then (p:ℝ)^a else 0) ∧
      ∀ (N : ℕ) (p : Fin N ↪ Nat.Primes) (a : ℝ) (ι : Type*) (L : Filter ι)
        (M : ι → Matrix (Fin N) (Fin N) ℂ),
        (∀ i j, Tendsto (fun u => M u i j) L
          (𝓝 (((Real.log (p i : ℝ)) * ∑' k : ℤ, (((p i : ℝ)^(-k))^a) * f (p j) ((p i : ℝ)^(-k)) : ℝ) : ℂ))) →
        ∀ᶠ u in L,
          (∀ (d : ℕ) (A : Matrix (Fin N) (Fin d) ℂ) (B : Matrix (Fin d) (Fin N) ℂ),
            M u = A * B → N ≤ d) ∧
          ∀ (μ : Measure ℝ) (W V : Fin N → ℝ → ℂ),
            (∀ i j, Integrable (fun t => W i t * V j t) μ) →
            (∀ i j, M u i j = ∫ t, W i t * V j t ∂μ) →
            ∀ c : Fin N → ℂ, (∀ᵐ t ∂μ, ∑ i, c i * W i t = 0) → c = 0 := by sorry

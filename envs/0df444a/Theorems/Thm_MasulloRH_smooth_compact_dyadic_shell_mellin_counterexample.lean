-- Prove2me | Theorems.Thm_MasulloRH_smooth_compact_dyadic_shell_mellin_counterexample
-- name    : MasulloRH.smooth_compact_dyadic_shell_mellin_counterexample
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:41:15.890408+00:00
-- url     : https://prove2.me/theorems/1d740792-b9e7-4ef3-bb42-6512e73025f5
-- title:
--   A smooth compactly supported counterexample to exchanging the dyadic sieve limit and the half-Mellin integral
-- statement:
--   There exist smooth compactly supported real functions $\psi,g$ such that $\psi$ vanishes outside $(0,8)$ and has additive integral zero on $(0,\infty)$. Let $F(t)=\sum_{n\ge1}\psi(nt)$, let $Q_B$ be the odd primes up to $B$, and define the corrected even shell
--   $$
--   G_B(t)=\sum_{U\subseteq Q_B}(-1)^{|U|}F\!\left(2\prod_{q\in U}q\,t\right).
--   $$
--   The pure dyadic sum $\sum_{j\ge1}\psi(2^jt)$ equals $g(t)$ at every $t>0$. For every $\delta>0$, all sufficiently large $B$ satisfy $G_B(t)=g(t)$ simultaneously for every $t\ge\delta$. Each $G_B$ has an absolutely convergent Mellin integral at $1/2$, and those integrals tend to zero. Yet $g$ has an absolutely convergent, nonzero Mellin integral at $1/2$.
-- source:
--   Scalar norm-section test for the global prime cutoff in Masullo, The Music of the Primes, Chapter 11, §11.3. Builds on the accepted Prove2Me theorem MasulloRH.corrected_prime_shell_mellin_limits (6e438335-bf6f-44ab-b3d2-ee04d67ae833), together with a compact-support bump, composite trapezoidal error estimate, finite inclusion–exclusion and dyadic telescoping.

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Nat.Prime.Basic

open Finset Filter Set MeasureTheory
open scoped Topology

theorem MasulloRH.smooth_compact_dyadic_shell_mellin_counterexample :
    ∃ ψ g : ℝ → ℝ,
      let F (t : ℝ) : ℂ := ∑' n : ℕ, (ψ (((n:ℝ)+1)*t) : ℂ)
      let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2)
      let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
        (-1:ℂ)^U.card * F ((2*∏ l ∈ U, (l:ℝ))*t)
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      (∀ t : ℝ, t ≤ 0 ∨ 8 ≤ t → ψ t = 0) ∧
      (∫ t in Ioi (0:ℝ), ψ t) = 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ t : ℝ, 0 < t → (∑' j : ℕ, (ψ (2^(j+1)*t):ℂ)) = (g t : ℂ)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ B : ℕ in atTop, ∀ t : ℝ, δ ≤ t → G B t = (g t : ℂ)) ∧
      (∀ B : ℕ, MellinConvergent (G B) (1/2:ℂ)) ∧
      Tendsto (fun B : ℕ => mellin (G B) (1/2:ℂ)) atTop (𝓝 0) ∧
      MellinConvergent (fun t : ℝ => (g t : ℂ)) (1/2:ℂ) ∧
      mellin (fun t : ℝ => (g t : ℂ)) (1/2:ℂ) ≠ 0 := by sorry

-- Prove2me | Theorems.Thm_MasulloRH_padic_product_norm_cutoff_rigidity_and_rank
-- name    : MasulloRH.padic_product_norm_cutoff_rigidity_and_rank
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:41:49.877366+00:00
-- url     : https://prove2.me/theorems/2779aee5-75c7-4b20-ab08-ee25a3e9be68
-- title:
--   Product-norm cutoffs on the real and p-adic places: infinite tensor rank and a bounded-window period
-- statement:
--   For every rational prime $p$ put $F_m(x,y)=e^{-x^2}\mathbf1_{\|y\|_p\le1}m(|x|\|y\|_p)$ on $\mathbf R\times\mathbf Q_p$. There is a neighborhood of $y=0$ on which all real slices take their value at zero if and only if $m$ is constant on $[0,\infty)$. A common open additive period group or a finite separated sum with locally constant $p$-adic factors forces that same constancy. If $m(a)\ne0$ for some $a>0$ and $m=0$ above a finite positive threshold, $F_m$ has infinite tensor rank even on $x>0,\,\|y\|_p\le1$, with arbitrary complex factors. In particular a smooth compact cutoff taking values between zero and one, equal to one on $[-1,1]$ and to zero outside $(-2,2)$, witnesses all three failures.
--
--   Conversely, if an input $f$ is supported in $|x|\le X$ and invariant under $p$-adic shifts of norm at most $d$, multiplying by $m(|x|\|y\|_p)$ preserves all periods of norm at most $\min(d,\delta/X)$ whenever $m$ is constant on $[0,\delta]$ and $X,\delta,d>0$.
-- source:
--   A two-place test of the S-norm Fourier cutoff in Masullo, The Music of the Primes, Chapter 12, §12.4. The distinction is between the algebraic finite tensor of local test spaces and an operator acting on a larger completion.

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Set
open scoped Topology

theorem MasulloRH.padic_product_norm_cutoff_rigidity_and_rank (p : ℕ) [Fact p.Prime] :
    let F (m : ℝ → ℝ) (x : ℝ) (y : ℚ_[p]) : ℂ :=
      if ‖y‖ ≤ 1 then (Real.exp (-(x^2)):ℂ) * (m (|x| * ‖y‖):ℂ) else 0
    let UniformAtZero (m : ℝ → ℝ) := ∀ᶠ y in 𝓝 (0:ℚ_[p]), ∀ x : ℝ, F m x y = F m x 0
    let CommonPeriod (m : ℝ → ℝ) := ∃ H : AddSubgroup ℚ_[p], IsOpen (H : Set ℚ_[p]) ∧
      ∀ (x : ℝ) (y h : ℚ_[p]), h ∈ H → F m x (y+h) = F m x y
    let FiniteLoc (m : ℝ → ℝ) := ∃ (n : ℕ) (a : Fin n → ℝ → ℂ) (b : Fin n → ℚ_[p] → ℂ),
      (∀ i, IsLocallyConstant (b i)) ∧ ∀ x y, F m x y = ∑ i, a i x * b i y
    let FiniteOnBall (m : ℝ → ℝ) := ∃ (n : ℕ) (a : Fin n → ℝ → ℂ) (b : Fin n → ℚ_[p] → ℂ),
      ∀ x : ℝ, 0<x → ∀ y : ℚ_[p], ‖y‖≤1 → F m x y = ∑ i, a i x * b i y
    (∀ m : ℝ → ℝ, (UniformAtZero m ↔ ∀ t : ℝ, 0 ≤ t → m t = m 0) ∧
      (CommonPeriod m → ∀ t : ℝ, 0 ≤ t → m t = m 0) ∧
      (FiniteLoc m → ∀ t : ℝ, 0 ≤ t → m t = m 0) ∧
      (∀ a C : ℝ, 0<a → 0<C → m a ≠ 0 → (∀ t : ℝ, C≤t → m t=0) → ¬FiniteOnBall m)) ∧
    (∀ (m : ℝ → ℝ) (X δ d : ℝ), 0<X → 0<δ → 0<d →
      (∀ t : ℝ, 0 ≤ t → t ≤ δ → m t = m 0) →
      ∀ f : ℝ → ℚ_[p] → ℂ, (∀ x, X < |x| → ∀ y, f x y = 0) →
      (∀ x y h, ‖h‖ ≤ d → f x (y+h) = f x y) →
      ∀ (x : ℝ) (y h : ℚ_[p]), ‖h‖ ≤ min d (δ/X) →
        (m (|x| * ‖y+h‖):ℂ) * f x (y+h) = (m (|x| * ‖y‖):ℂ) * f x y) ∧
    ∃ m : ℝ → ℝ, ContDiff ℝ (⊤:ℕ∞) m ∧ HasCompactSupport m ∧
      (∀ t, 0 ≤ m t ∧ m t ≤ 1) ∧ (∀ t : ℝ, |t| ≤ 1 → m t = 1) ∧
      (∀ t : ℝ, 2 ≤ |t| → m t = 0) ∧
      ¬UniformAtZero m ∧ ¬CommonPeriod m ∧ ¬FiniteLoc m ∧ ¬FiniteOnBall m := by sorry

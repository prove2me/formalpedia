-- Prove2me | Theorems.Thm_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
-- name    : MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/a5464751-9aa6-5527-8b7f-2438bde9862b
-- title:
--   Borel's lemma with smooth compactly supported parameters
-- statement:
--   Let $E$ be a finite-dimensional real normed space (a normed additive commutative group with a real normed space structure, finite-dimensional over $\mathbb{R}$) and let $F$ be a complete real normed space. Let $C \subseteq E$ be a compact set, and let $a : \mathbb{N} \to E \to F$ be a sequence of maps such that each $a_k$ is $C^\infty$ on $E$ (smooth of order $\top$ for the real field) and each $a_k$ vanishes at every point $e \notin C$. The assertion is that there exists $B : E \times \mathbb{R} \to F$, smooth of order $\top$ over $\mathbb{R}$, with the following property: for all natural numbers $n$ and $m$ with $m \le n$, and for every $e \in E$, the $m$-th iterated Fréchet derivative of the map
--   $$(e', \rho) \mapsto B(e', \rho) - \sum_{k=0}^{n} \frac{\rho^{k}}{k!}\, a_k(e')$$
--   vanishes at the point $(e, 0)$. Thus $B$ has, along the hyperplane $\rho = 0$, the prescribed Taylor coefficients $a_k$ in all variables jointly: all derivatives of order at most $n$ of the difference with the $n$-th partial Taylor sum vanish on $E \times \{0\}$.
--
--   This is Borel's lemma in a version with parameters: an arbitrary sequence of smooth maps supported in a fixed compact set is realised as the jet along $\rho = 0$ of a single smooth function of $(e,\rho)$. It supplies the analytic half of the extension of smooth functions from a half-space, and is used by [`MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace`](thm.html#MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (C : Set E) (hC : IsCompact C)
    (a : ℕ → E → F) (ha : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) (hsupp : ∀ k (e : E), e ∉ C → a k e = 0) :
    ∃ B : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDeriv ℝ m
          (fun p : E × ℝ => B p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1) (e, 0) = 0 := by sorry

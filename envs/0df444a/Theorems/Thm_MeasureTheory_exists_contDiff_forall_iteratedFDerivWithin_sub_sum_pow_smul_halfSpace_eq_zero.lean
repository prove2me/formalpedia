-- Prove2me | Theorems.Thm_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
-- name    : MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/89d8b5ae-0f24-5543-b057-cbd874f63dff
-- title:
--   Taylor osculation along the boundary of a half-space
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F$ a real Banach space. Let $\Psi : E \times \mathbb{R} \to F$ be a function which is $C^\infty$ in the relative sense on the closed half-space $H = \{p \in E\times\mathbb{R} : 0 \le p_2\}$, and let $C \subseteq E$ be compact with $\Psi(p) = 0$ whenever $p_1 \notin C$. The assertion is that there exists a sequence of functions $a_k : E \to F$, $k \in \mathbb{N}$, such that: each $a_k$ is $C^\infty$ on all of $E$; each $a_k$ vanishes outside $C$, i.e. $a_k(e) = 0$ for $e \notin C$; and for all natural numbers $n$ and $m$ with $m \le n$ and every $e \in E$, the $m$-th iterated Fréchet derivative within $H$ of the remainder $$p \mapsto \Psi(p) - \sum_{k=0}^{n} \frac{p_2^{\,k}}{k!}\, a_k(p_1)$$ vanishes at the boundary point $(e,0)$. Thus the partial sums $\sum_{k \le n} \rho^k a_k(e)/k!$ osculate $\Psi$ to order $n$ along $\rho = 0$, as multilinear derivatives within the half-space.
--
--   This is the bookkeeping half of the Borel–Seeley construction with parameters: the normal Taylor coefficients $a_k(e) = \partial_\rho^k \Psi(e,0^+)$ of a function smooth up to the boundary of a half-space, together with the statement that each truncated Taylor series agrees with $\Psi$ to the corresponding order at the boundary. It feeds the construction of a smooth extension across the boundary, [`MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace`](thm.html#MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace), and relies on the full permutation symmetry of iterated derivatives within a convex set with nonempty interior.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0) :
    ∃ a : ℕ → E → F, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k (e : E), e ∉ C → a k e = 0) ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDerivWithin ℝ m
          (fun p : E × ℝ => Ψ p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1)
          {p : E × ℝ | 0 ≤ p.2} (e, 0) = 0 := by sorry

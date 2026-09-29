-- Prove2me | Theorems.Thm_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
-- name    : MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/47b24167-67e2-54e6-bbd4-d892636817a7
-- title:
--   Boundary jet on a half-space realised by a smooth function
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F$ a real Banach space, let $H=\{p\in E\times\mathbb R: 0\le p_2\}$ be the closed half-space, and let $\Psi:E\times\mathbb R\to F$ be smooth on $H$ in the sense of `ContDiffOn ℝ ⊤ Ψ H`. Suppose $C\subseteq E$ is compact and $\Psi$ vanishes at every point $p$ whose first coordinate lies outside $C$. Then there exists $B:E\times\mathbb R\to F$, smooth on all of $E\times\mathbb R$ (`ContDiff ℝ ⊤ B`), such that for every $n\in\mathbb N$ and every $e\in E$ the $n$-th iterated Fréchet derivative of $B$ at $(e,0)$ coincides, as a continuous multilinear map $(E\times\mathbb R)^n\to F$, with the $n$-th iterated Fréchet derivative of $\Psi$ at $(e,0)$ taken relative to $H$, i.e. `iteratedFDeriv ℝ n B (e, 0) = iteratedFDerivWithin ℝ n Ψ H (e, 0)`. No support condition is asserted for $B$, and the equality of derivatives is asserted only along the boundary hyperplane $E\times\{0\}$, not at interior points.
--
--   This is Borel's lemma with parameters, equivalently the jet-theoretic content of Seeley's extension theorem for $C^\infty$ functions on a half-space: the boundary Taylor jet of a function smooth up to the boundary is realised by a globally smooth function. It is used in the construction of smooth decompositions of integrals involving $\log(x^2+y^2)$-type kernels, namely by the two results on compactly supported smooth integrands that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0) :
    ∃ B : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (n : ℕ) (e : E),
        iteratedFDeriv ℝ n B (e, 0) = iteratedFDerivWithin ℝ n Ψ {p : E × ℝ | 0 ≤ p.2} (e, 0) := by sorry

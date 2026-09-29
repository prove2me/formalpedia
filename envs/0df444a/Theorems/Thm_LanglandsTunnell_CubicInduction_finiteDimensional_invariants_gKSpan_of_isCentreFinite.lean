-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite
-- name    : LanglandsTunnell.CubicInduction.finiteDimensional_invariants_gKSpan_of_isCentreFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/c8aca8c9-492c-5a61-a5b6-1e10c9bbeb02
-- title:
--   Rotation invariants in the mathfrakgl₃-span of f are finite-dimensional
-- statement:
--   Let $f$ be a complex-valued function on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$. Call $k$ *orthogonal at infinity* if its component at every height-one prime of $\mathcal{O}_{\mathbb{Q}}$ is the identity and its archimedean component $\kappa$ satisfies $\kappa^{\mathsf{T}}\kappa = 1$; write $T_f$ for the complex span of the translates $g \mapsto f(gk)$ over such $k$, and $M_f$ for the submodule that the universal enveloping algebra of $\mathfrak{gl}_3(\mathbb{C})$, acting by the right derivatives $\mathrm{archDeriv}$ at the infinite place, generates inside the archimedean-smooth functions from those elements of $T_f$ that are archimedean-smooth. Assume: (i) finitely many functions whose complex span contains every translate $g \mapsto f(gk)$ with $k$ orthogonal at infinity; (ii) for each $\varphi \in T_f$ and each of the three operators $\varphi \mapsto \sum_i D_{ii}\varphi$, $\sum_{i,j} D_{ij}D_{ji}\varphi$, $\sum_{i,j,k} D_{ij}D_{jk}D_{ki}\varphi$ (with $D_{ij} = \mathrm{archDeriv}\,i\,j$), the iterates of that operator on $\varphi$ satisfy a monic linear relation $\sum_m a_m \cdot (\text{iterate}^m \varphi) = 0$ with top coefficient $1$; (iii) every archimedean-smooth element of $T_f$ is killed by the derivative along each $E_{ij} - E_{ji}$; (iv) a form $B$ on the archimedean-smooth functions which, on $M_f$, is $\mathbb{C}$-linear in its first argument, conjugate-symmetric, has $\operatorname{Re} B(w,w) > 0$ for $w \neq 0$, and makes each derivative along $E_{ij} - E_{ji}$ skew-adjoint. Then the complex subspace of $M_f$ annihilated by all the derivatives along the matrices $E_{ij} - E_{ji}$, $i, j \in \{0,1,2\}$, is finite-dimensional over $\mathbb{C}$.
--
--   This is the trivial-type case of admissibility in the sense of Harish-Chandra: the vectors of $M_f$ killed by $\mathfrak{so}_3$ form the trivial isotypic component, and the assertion is that it is finite-dimensional. Unlike the classical statement, local finiteness under $\mathfrak{so}_3$ is not assumed but replaced by the positive skew-adjoint form $B$ and by centre-finiteness on all of $T_f$; the result feeds into [`LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule`](thm.html#LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_KFinite3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open scoped LanglandsTunnell.CubicInduction.WhittakerBlock in

theorem
LanglandsTunnell.CubicInduction.finiteDimensional_invariants_gKSpan_of_isCentreFinite
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hfin : WhittakerBlock.IsOrthFinite f)
    (hcentre : ∀ φ ∈ WhittakerBlock.orthSpan f, WhittakerBlock.IsCentreFinite φ)
    (hrot : ∀ i j : Fin 3, ∀ φ : WhittakerBlock.smoothFunctions3,
      (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ WhittakerBlock.orthSpan f →
        WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) φ = 0)
    (B : WhittakerBlock.smoothFunctions3 → WhittakerBlock.smoothFunctions3 → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ WhittakerBlock.gKSpan f, ∀ w₂ ∈ WhittakerBlock.gKSpan f, ∀ w' ∈ WhittakerBlock.gKSpan f,
      B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ WhittakerBlock.gKSpan f, ∀ w' ∈ WhittakerBlock.gKSpan f, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ WhittakerBlock.gKSpan f, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ i j : Fin 3, ∀ x ∈ WhittakerBlock.gKSpan f, ∀ y ∈ WhittakerBlock.gKSpan f,
      B (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) x) y =
        -B x (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) y)) :
    FiniteDimensional ℂ ↥((WhittakerBlock.gKSpan f).restrictScalars ℂ ⊓
      ⨅ i : Fin 3, ⨅ j : Fin 3,
        LinearMap.ker (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1))) := by sorry

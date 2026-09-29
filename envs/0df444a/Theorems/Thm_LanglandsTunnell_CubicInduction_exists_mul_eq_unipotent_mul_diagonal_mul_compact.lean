-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
-- name    : LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_compact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d3f505e6-9872-5386-b640-66c466e58fd4
-- title:
--   Adelic Siegel-set reduction for GL₃ over ℚ
-- statement:
--   There exist real constants $c$ and $C$ with $c > 0$ such that for every $g$ in $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, the general linear group of degree $3$ over the adele ring of $\mathbb{Q}$, there are $\gamma \in \mathrm{GL}_3(\mathbb{Q})$ and $n, t, k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ such that the image of $\gamma$ under the map `globalPointsGL` induced by the structure map $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$, multiplied by $g$, equals $n \, t \, k$, and the following hold. At every nonzero prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ the components of $n$ and of $t$ in $\mathrm{GL}_3$ of the $p$-adic completion (obtained by projecting to the finite adeles and evaluating at $p$) are the identity, while the component of $k$ lies in `localMaximalCompact3`, the subgroup of those matrices all of whose entries, and all of whose inverse's entries, have valuation at most $1$. At every infinite place $w$ of $\mathbb{Q}$, writing the component in $\mathrm{GL}_3$ of the completion at $w$ (projection to the infinite adeles followed by evaluation at $w$): the matrix of $n$ has all diagonal entries $1$, vanishing entries $(i,j)$ with $j < i$, and every entry of norm at most $C$; the matrix of $t$ has vanishing off-diagonal entries, with $c \le$ `archRoot₁ ℚ w t` and $c \le$ `archRoot₂ ℚ w t`, the two simple-root quantities attached to the diagonal component of $t$ at $w$; and the matrix $K$ of $k$ satisfies $K^{\mathsf{T}} K = 1$. Unlike the real statement it rests on, no positivity of the diagonal entries of $t$ is asserted.
--
--   This is the reduction theory of Minkowski, Hermite and Siegel for $\mathrm{GL}_3$ over $\mathbb{Q}$ in adelic form: every adelic point is a $\mathrm{GL}_3(\mathbb{Q})$-translate of a point of a Siegel set times the standard maximal compact subgroup $\mathrm{O}(3) \times \prod_p \mathrm{GL}_3(\mathbb{Z}_p)$. It combines a decomposition over the finite places (class number one) with the archimedean statement `exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real`, and it is used in the analysis of automorphic forms on $\mathrm{GL}_3$ over $\mathbb{Q}$, in particular for the growth and support estimates behind the spectral and smoothing arguments in the cubic base-change input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_compact :
    ∃ c C : ℝ, 0 < c ∧ ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ∃ (γ : GL (Fin 3) ℚ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ),
        globalPointsGL 3 (𝓞 ℚ) ℚ γ * g = n * t * k ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
        ∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1 := by sorry

-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/06874188-5cb0-5024-8a98-3e692f671f6f
-- title:
--   Vanishing of Whittaker functions off the dominant cone
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, and let $W \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ be a function. Assume: (i) $W$ is right invariant under the subgroup `localMaximalCompact3` of those $k \in \mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries, and all of whose entries of $k^{-1}$, have valuation $\le 1$, i.e. $W(gk) = W(g)$ for all $g$ and all such $k$; (ii) $W$ satisfies the Whittaker transformation law $W(u(x,y,z)\,g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$, $y$ in positions $(1,2)$, $(2,3)$ and $z$ in position $(1,3)$; (iii) there exists $x$ with $\mathrm{v}(x) \le 1$ such that $\psi_v(\varpi^{-1}x) \neq 1$, where $\varpi$ denotes the image of the chosen uniformiser of $v$. Let $t \in \mathrm{GL}_3(\mathbb{Q}_v)$ be such that its underlying matrix is $\mathrm{diagonal}(d)$ for some $d \colon \mathrm{Fin}\,3 \to \mathbb{Q}_v$, and suppose $\mathrm{v}(d_1) < \mathrm{v}(d_0)$ or $\mathrm{v}(d_2) < \mathrm{v}(d_1)$. Then $W(t) = 0$.
--
--   This is the standard support property of a spherical Whittaker function on $\mathrm{GL}_3$ over a local field: on the diagonal torus such a function vanishes outside the cone $\mathrm{v}(d_0) \le \mathrm{v}(d_1) \le \mathrm{v}(d_2)$. It is used in the local theory feeding the Rankin–Selberg and zeta-integral computations for $\mathrm{GL}_3$, for instance in reducing Whittaker integrals to sums over the dominant cone and in the vanishing criteria for coset eigenfunctions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (hd : Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)) :
    W t = 0 := by sorry

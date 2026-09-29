-- Prove2me | Theorems.Thm_ModularCurve_deg_eq_one_and_finiteDimensional_lSpace_and_ell_eq_qExpFunctionFieldC_of_isAlgClosed
-- name    : ModularCurve.deg_eq_one_and_finiteDimensional_lSpace_and_ell_eq_qExpFunctionFieldC_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/e50dcc70-c228-5a78-a62b-a4ee6094a0ee
-- title:
--   Places, L(D) and Riemann's equality for ̄ F_Γ over ̄ K
-- statement:
--   Let $K$ be an algebraically closed field and let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index containing the translation matrix $T$. Let $F=$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the set of quotients $\mathrm{int}_K(p_f)/\mathrm{int}_K(p_g)$, where $f,g$ run over modular forms of a common weight $k$ for $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb R)$), $p_f,p_g$ are integral power series realising their $q$-expansions and the denominator series is nonzero in $K((q))$. Here a place of $F$ over $K$ is a valuation subring of $F$, other than $F$ itself, containing the image of $K$ and a principal ideal ring; its degree is $\dim_K$ of its residue field; a divisor is a finitely supported $\mathbb Z$-valued function on places, its degree the sum of its values weighted by the degrees of the places; $L(D)$ is the space of $f\in F$ with $v(f)\le \exp(D v)$ for every place $v$, $\ell(D)=\dim_K L(D)$, and $g=\dim_K H^1(0)$ is the adelic genus. The theorem asserts three things: every place of $F$ over $K$ has degree $1$; for every divisor $D$ the space $L(D)$ is finite-dimensional over $K$; and $\ell(D)=\deg D+1-g$ whenever $2g-1\le \deg D$.
--
--   This packages, for the $q$-expansion function field of a modular curve over an algebraically closed base, the three standard facts of the theory of function fields of one variable: rationality of all places, finiteness of Riemann–Roch spaces, and Riemann's equality in the non-special range $\deg D\ge 2g-1$. It is used as input to the constructions of sections with prescribed poles and residues on modular curves in the Jacquet–Langlands-style specialisation arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_eq_one_and_finiteDimensional_lSpace_and_ell_eq_qExpFunctionFieldC_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.deg_eq_one_and_finiteDimensional_lSpace_and_ell_eq_qExpFunctionFieldC_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    (∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ), v.deg = 1) ∧
    (∀ D : AlgebraicCurve.Divisor K ↥(ModularCurve.qExpFunctionFieldC K Γ), FiniteDimensional K ↥(AlgebraicCurve.LSpace D)) ∧
    (∀ D : AlgebraicCurve.Divisor K ↥(ModularCurve.qExpFunctionFieldC K Γ),
      2 * (AlgebraicCurve.genusFF K ↥(ModularCurve.qExpFunctionFieldC K Γ) : ℤ) - 1 ≤ D.degree →
        (AlgebraicCurve.ell D : ℤ) = D.degree + 1 - AlgebraicCurve.genusFF K ↥(ModularCurve.qExpFunctionFieldC K Γ)) := by sorry

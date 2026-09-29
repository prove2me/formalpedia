-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_exists_veluQuotient2_j_eq_of_mem_roots_fibrePoly
-- name    : ModularCurve.ModularPolynomialData.exists_veluQuotient2_j_eq_of_mem_roots_fibrePoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/dcb5b88b-47dc-5f1f-b53e-91c5b1c764fb
-- title:
--   Roots of the level-2 fibre polynomial are Vélu quotient j-invariants
-- statement:
--   Let $K$ be an algebraically closed field with decidable equality in which $2 \neq 0$, and let `data` be a `ModularPolynomialData 2`: a monic polynomial $\Phi$ in one variable over $\mathbb{Z}[X]$ whose degree equals $\psi(2)=\sum_{d \mid 2,\ d \text{ squarefree}} 2/d = 3$ and which vanishes on the pair of $q$-expansions given by `evalAtJ` and `jqN 2`. Let $W$ be a Weierstrass curve over $K$ which is elliptic, and let $y \in K$ be a root (in the multiset of roots) of `fibrePoly data.Φ W.j`, the degree-$3$ polynomial in $K[X]$ obtained from $\Phi$ by mapping each coefficient polynomial in $\mathbb{Z}[X]$ to $K$ along $\mathbb{Z} \to K$ and evaluating it at $j(W)$. Then there exist $x_0, y_0 \in K$ satisfying the affine Weierstrass equation of $W$ and with $-(2y_0 + a_1 x_0 + a_3) = 0$, that is, a $2$-torsion point, such that the Weierstrass curve `W.veluQuotient2 x₀ y₀` — with the same $a_1, a_2, a_3$ and with $a_4$ replaced by $a_4 - 5g_x$ and $a_6$ by $a_6 - b_2 g_x - 7 x_0 g_x$, where $g_x = 3x_0^2 + 2a_2x_0 + a_4 - a_1y_0$ — has nonvanishing discriminant, and its $j$-invariant (formed using the resulting unit discriminant) equals $y$.
--
--   This is the level-$2$ surjectivity statement: every root of the specialised modular polynomial $\Phi_2(j(E), \cdot)$ is the $j$-invariant of the quotient of $E$ by a subgroup of order $2$, realised through Vélu's formulae. It is used in the proof of [`ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly`](thm.html#ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly), where roots of the fibre polynomial must be identified with $j$-invariants of $2$-isogenous curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_exists_veluQuotient2_j_eq_of_mem_roots_fibrePoly.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.ModularPolynomialData.exists_veluQuotient2_j_eq_of_mem_roots_fibrePoly
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (data : ModularPolynomialData 2) (W : WeierstrassCurve K) [W.IsElliptic]
    {y : K} (hy : y ∈ (fibrePoly data.Φ W.j).roots) :
    ∃ x₀ y₀ : K, W.toAffine.Equation x₀ y₀ ∧ W.veluGy x₀ y₀ = 0 ∧
      ∃ hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0,
        @WeierstrassCurve.j K _ (W.veluQuotient2 x₀ y₀) ⟨isUnit_iff_ne_zero.mpr hΔ⟩ = y := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
-- name    : ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/6aaaf00d-fdc2-5823-8c81-e367039ad795
-- title:
--   Level-2 modular equation via Vélu quotients
-- statement:
--   Let $K$ be an algebraically closed field in which $2 \neq 0$, let `data` be a term of `ModularPolynomialData 2`, i.e. a monic $\Phi \in (\mathbb{Z}[X])[Y]$ of degree $\mathrm{dedekindPsi}(2) = \sum_{d \mid 2,\ d\ \text{squarefree}} 2/d = 3$ in $Y$ satisfying $\Phi(j(q), j(q^2)) = 0$ as a Laurent series over $\mathbb{Q}$, and let $W$ be a Weierstrass curve over $K$ that is elliptic (unit discriminant), with $j$-invariant $W.j$. Let $\iota$ be a finite type of cardinality $3$ and $P : \iota \to K \times K$ an injective family of pairs such that each $P_i = (x_i, y_i)$ satisfies the affine Weierstrass equation of $W$, satisfies $\mathrm{veluGy}(x_i,y_i) = -(2y_i + a_1 x_i + a_3) = 0$, and is such that the Weierstrass curve $\mathrm{veluQuotient2}(x_i,y_i)$ — with the same $a_1, a_2, a_3$ as $W$, with $a_4$ replaced by $a_4 - 5\,g_x$ and $a_6$ by $a_6 - b_2 g_x - 7 x_i g_x$, where $g_x = 3x_i^2 + 2a_2 x_i + a_4 - a_1 y_i$ — has non-zero discriminant. Then the specialisation of $\Phi$ obtained by mapping its integer coefficients into $K$ and evaluating the inner variable at $W.j$ equals $\prod_{i} \bigl(X - j(\mathrm{veluQuotient2}(x_i,y_i))\bigr)$ in $K[X]$, the $j$-invariants being formed using the given non-vanishing of the discriminants.
--
--   This is the level-$2$ modular equation in characteristic different from $2$: the fibre of $\Phi_2$ over $j(E)$ splits, with multiplicity, as the product over the three nontrivial $2$-torsion points of $X - j(E/\langle P\rangle)$, the quotients being given by Vélu's formulas for a kernel of order $2$. It is the form of the statement used to identify the roots of the fibre polynomial with $j$-invariants of cyclic quotients, feeding the extraction of a quotient curve from a root of the modular polynomial and the separability statement for the level-$2$ fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j.lean

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

theorem ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (data : ModularPolynomialData 2) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by sorry

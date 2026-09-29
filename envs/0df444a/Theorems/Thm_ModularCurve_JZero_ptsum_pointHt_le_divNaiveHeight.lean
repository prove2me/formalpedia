-- Prove2me | Theorems.Thm_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight
-- name    : ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/83d0c611-0fff-522c-9a11-365503ff2c77
-- title:
--   Point heights of a representative bounded by its naive height
-- statement:
--   Let $N\ge 1$, let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, and let $s=(s_i)_{i<r}$ be a family in the function field $\overline{M}_N$ = `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$) which is an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space $\{f : v(f)\le \exp(D(v))$ for all places $v\}$ of the divisor $D=(\mathrm{embDegree}\ N)\cdot \overline{\infty}$, where $\overline{\infty}=$ `cuspInftyBar N`. Then there exists $B\ge 0$ such that for every $n\in\mathbb{N}$ there is a constant $C_1$ with the following property. Let $c$ be an element of the subgroup of $\mathrm{Pic}^0(\overline{M}_N)$ fixed pointwise by the subgroup of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $K$, and let $D$ be a divisor of $\overline{M}_N$ which represents $c$ at degree $n$ in the sense of `JZero.IsRepOf`: there is a degree-zero divisor $E$ with $D$ effective, $E+n\,\overline{\infty}=D$, $D$ invariant under the action through `arithmeticGalois` of every $\sigma$ fixing $K$, and the class of $E$ equal to $c$. Then
--   $$\sum_{v\neq\overline{\infty}} D(v)\,h_s(v)\ \le\ B\cdot \mathrm{divNaiveHeight}\ N\ K\ n\ D+C_1,$$
--   the sum being over the support of $D$ with $\overline{\infty}$ removed, where $h_s(v)=$ `pointHt s v` is the absolute logarithmic height of the vector $\bigl(v(s_i\,s_{i_0}^{-1})\bigr)_i$ obtained by evaluating $s$ at $v$ after normalising by a pivot coordinate, and `divNaiveHeight N K n D` is the logarithmic height of the vector $(\mathrm{symVec}\ N\ n\ D\ k)_{k<n+1}$ read in $K$ (and $0$ if its entries do not lie in $K$). The slope $B$ depends only on $N$, $K$ and $s$; only the additive constant $C_1$ may depend on $n$.
--
--   This is the comparison, uniform in the degree, between the sum of the point heights of the non-cuspidal part of a Galois-stable effective representative and the naive height of that representative, built from the symmetric functions of its $j$-coordinates. It feeds the construction of the height form on the degree-zero class group, being cited by [`ModularCurve.JZero.heightForm_le`](thm.html#ModularCurve.JZero.heightForm_le) and by the two quasi-invariance estimates for that form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight.lean

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∃ C₁ : ℝ,
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        JZero.IsRepOf N K n c D →
        ((D.erase (cuspInftyBar N)).sum fun v m => (m : ℝ) * pointHt s v)
          ≤ B * divNaiveHeight N K n D + C₁ := by sorry

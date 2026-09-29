-- Prove2me | Theorems.Thm_ModularCurve_JZero_heightForm_le
-- name    : ModularCurve.JZero.heightForm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/ba26f469-623a-5341-9227-f732de6391e9
-- title:
--   Height form bounded above by naive height of representatives
-- statement:
--   Fix $N\ge 1$, a subfield $K$ of $\overline{\mathbb{Q}}$ finite over $\mathbb{Q}$, and a natural number $g'$. Let $s=(s_0,\dots,s_{r-1})$ be a family of elements of `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside Laurent series, and assume `IsEmbBasis N s`: the $s_i$ are linearly independent over $\overline{\mathbb{Q}}$ and their span is the Riemann–Roch space $\mathcal{L}(\,$`embDivisor N`$\,)$, i.e. the space of $f$ with $v$-adic valuation at most $\exp(\mathrm{embDivisor}\,N\,(v))$ at every place $v$. Then there are real constants $c_1$ and $C$ with the following property. Let $c$ be a class in $\mathrm{Pic}^0$ of `modularFunctionFieldBar N` fixed by the subgroup of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ fixing $K$ pointwise, acting through `arithmeticGalois`, and let $D$ be a divisor with `JZero.IsRepOf N K g' c D`: there is a degree-zero divisor $E$ with all coefficients of $D$ non-negative, $E+g'\cdot[\,$`cuspInftyBar N`$\,]=D$, with $D$ invariant under that subgroup, and with class of $E$ equal to $c$. Then $$\mathrm{heightForm}(s,\mathrm{genusFF},\mathrm{cuspInftyBar}\,N,D)\le c_1\,\mathrm{divNaiveHeight}(N,K,g',D)+C,$$ where the left side is the explicit quadratic expression `heightFormAux` in the base heights `baseHt` and pairwise heights `pairHt` of the points of $D$ with the cusp removed, and the right side is the logarithmic height over $K$ of the vector `symVec N g' D` when its entries lie in $K$, and $0$ otherwise.
--
--   This is the upper half of the comparison between the quadratic height form attached to an embedding basis of the modular curve of level $N$ and the naive height of the symmetric-function vector of a representative divisor, the constants depending on $N$, $K$, $g'$ and $s$ but not on the class or its representative. It feeds into [`ModularCurve.JZero.naiveHeight_growth_of_prime_of_five_le`](thm.html#ModularCurve.JZero.naiveHeight_growth_of_prime_of_five_le), and its proof cites the degree-one statement for places of `modularFunctionFieldBar N`, invariance of the normalised logarithmic height under enlarging the base field, and the corresponding bound for the sum of point heights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_heightForm_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.heightForm_le (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₁ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), JZero.IsRepOf N K g' c D →
      JZero.heightForm N s D ≤ c₁ * divNaiveHeight N K g' D + C := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_isRepOf_heightForm_lower
-- name    : ModularCurve.JZero.exists_isRepOf_heightForm_lower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/8a35b5bf-c98e-5d97-905a-6de295e8d068
-- title:
--   Height form bounds the naive height from below
-- statement:
--   Fix a natural number $N \neq 0$, a subfield $K$ of $\overline{\mathbb{Q}}$ that is finite-dimensional over $\mathbb{Q}$, a natural number $g'$, and a finite family $s : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}(X_0(N))$ of elements of `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside Laurent series. Assume `IsEmbBasis N s`: the family $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space of the divisor `embDivisor N`. The assertion is the existence of reals $\eta, C$ with $\eta > 0$, depending only on these data and not on the class below, such that for every element $c$ of the subgroup of `JZero N` (the degree-zero divisor class group $\mathrm{Pic}^0$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$) fixed pointwise by `K.fixingSubgroup`, and for every divisor $D$ with `JZero.IsRepOf N K g' c D` — that is, $D$ is effective, invariant under the `arithmeticGalois` action of each $\sigma$ fixing $K$, and $D = E + g'\cdot[\,\infty\,]$ for a degree-zero divisor $E$ whose class is $c$, where $\infty$ is the place `cuspInftyBar N` — there is a further divisor $D_2$ with `JZero.IsRepOf N K g' c D₂` satisfying $$\eta \cdot \mathtt{divNaiveHeight}\,N\,K\,g'\,D_2 - C \le \mathtt{JZero.heightForm}\,N\,s\,D_2,$$ where the left-hand height is the logarithmic height over $K$ of the vector `symVec N g' D₂` (and $0$ if its entries do not all lie in $K$), and the right-hand side is the quadratic expression `heightFormAux` in the multiplicities of $D_2$ away from the cusp, formed from the local quantities `baseHt` and `pairHt` attached to $s$, with the genus `genusFF` as parameter.
--
--   This is the positivity half of the comparison between the quadratic height form attached to an embedding basis and the naive height of a divisor representing a Galois-stable class on $J_0(N)$: within each class one may choose a representative on which the height form dominates a positive multiple of the naive height, up to an additive constant. It is used in [`ModularCurve.JZero.heightForm_lower_of_prime_of_five_le`](thm.html#ModularCurve.JZero.heightForm_lower_of_prime_of_five_le), and feeds the construction of a height with the descent properties needed on $J_0(N)(K)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_isRepOf_heightForm_lower.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.exists_isRepOf_heightForm_lower (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (g' : ℕ)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ η C : ℝ, 0 < η ∧ ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), JZero.IsRepOf N K g' c D →
      ∃ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K g' c D₂ ∧
        η * divNaiveHeight N K g' D₂ - C ≤ JZero.heightForm N s D₂ := by sorry

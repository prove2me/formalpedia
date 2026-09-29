-- Prove2me | Theorems.Thm_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord
-- name    : ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/c781a471-1137-5a4b-97d8-712654d43c75
-- title:
--   Normalised Hahn-series embeddings at a place above j₀
-- statement:
--   Let $N$ be a nonzero natural number and $j_0 \in \overline{\mathbb Q}$. Write $F_N$ for `modularFunctionFieldBar N`, the subfield of the Laurent series field $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the elements of `modularFunctionFieldFull N`, the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the expansions `divisorExpansions N`; and write $\bar j$ for `jBar N`, the element of $F_N$ given by the $q$-expansion of $j$ with coefficients mapped into $\overline{\mathbb Q}$. The assertion is: for every place $w$ of $F_N$ over $\overline{\mathbb Q}$ — that is, a valuation subring of $F_N$ containing the image of $\overline{\mathbb Q}$, distinct from $F_N$ itself, and a principal ideal ring, with $\operatorname{ord}_w$ the associated normalised integer valuation — such that $\operatorname{ord}_w(\bar j - j_0) > 0$, the number of $\overline{\mathbb Q}$-algebra homomorphisms $\psi$ from $F_N$ to the field of Hahn series with rational exponents and coefficients in $\overline{\mathbb Q}$ which satisfy both $\psi(\bar j) = j_0 + t$, the constant series $j_0$ plus the single monomial of exponent $1$ with coefficient $1$, and the existence of a rational $g > 0$ with $g \cdot \operatorname{ord}_w(x) = \operatorname{order}(\psi x)$ for all $x \in F_N$, is equal to the natural number $\operatorname{ord}_w(\bar j - j_0)$.
--
--   This is the local count, at a single place of the function field of $X_0(N)$ lying over a point $j_0$ of the $j$-line, of the normalised Puiseux-type embeddings inducing that place: their number is the multiplicity of $j_0$ there. It is used in the computations of the fibre of $X_0(N) \to X(1)$ over $j_0$, in particular in the determinations of the numbers $\nu_2$ and $\nu_3$ of places where $\bar j - 1728$, respectively $\bar j$, has order one, and in the identification of the set of such embeddings modulo inducing the same place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_MazurStepThreeInputs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      Nat.card {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
        ∃ g : ℚ, 0 < g ∧ ∀ x, (w.ord x : ℚ) * g = (ψ x).order} =
      (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat := by sorry

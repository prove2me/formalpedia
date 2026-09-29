-- Prove2me | Theorems.Thm_ModularCurve_exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree
-- name    : ModularCurve.exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/a23fb177-48ae-5a56-a410-0513674b5953
-- title:
--   Jacobi inversion: effective representatives for classes of J₀(M)
-- statement:
--   Fix a natural number $M \neq 0$ and work with the field $F_M :=$ `modularFunctionFieldBar M`, the intermediate field of $\overline{\mathbf Q} \subseteq \mathrm{LaurentSeries}(\overline{\mathbf Q})$ obtained by adjoining to $\overline{\mathbf Q}$ the image, under the coefficientwise embedding of $\mathrm{LaurentSeries}(\mathbf Q)$, of the field $\mathbf Q(\mathrm{divisorExpansions}\,M)$. Divisors here are finitely supported $\mathbf Z$-valued functions on the set of places of $F_M$ over $\overline{\mathbf Q}$, a place being a proper valuation subring of $F_M$ containing $\overline{\mathbf Q}$ and being a principal ideal ring; the degree of a divisor is the sum of its coefficients weighted by the residue degrees of the places. Let $E_0$ be such a divisor whose degree is at least $\mathrm{genusFF}(\overline{\mathbf Q}, F_M)$, the $\overline{\mathbf Q}$-dimension of $H^1(0)$, and let $x$ be an element of $J_0(M) = \mathrm{Pic}^0$ of $F_M$, i.e. of the quotient of the group of degree-zero divisors by the subgroup of divisors of nonzero elements of $F_M$. Then there is a divisor $E$ with $E \geq 0$ coefficientwise, $\deg E = \deg E_0$, such that $E - E_0$ has degree zero and its class in $\mathrm{Pic}^0$ equals $x$.
--
--   This is Jacobi inversion in its weakest form: once the base divisor $E_0$ has degree at least the genus, every class of $J_0(M)$ is of the shape $[E - E_0]$ with $E$ effective of degree $\deg E_0$. It is used, at various levels $M$, by the steps that produce canonical effective representatives of divisor classes on modular curves, in particular in the construction of good divisors attached to prolongation and annulus data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree (M : ℕ) [NeZero M]
    (E₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M))
    (hg : (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) : ℤ) ≤ E₀.degree)
    (x : JZero M) :
    ∃ E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M), 0 ≤ E ∧
      E.degree = E₀.degree ∧
      ∃ hdeg : E - E₀ ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M)),
        Pic0.mk ⟨E - E₀, hdeg⟩ = x := by sorry

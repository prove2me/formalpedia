-- Prove2me | Theorems.Thm_ModularCurve_galois_smul_ofAlgAut_smul_of_fricke
-- name    : ModularCurve.galois_smul_ofAlgAut_smul_of_fricke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/1f5fbc1e-7502-508f-95e7-b451117835c4
-- title:
--   Fricke-type automorphism of J₀(N) commutes with Galois
-- statement:
--   Let $N$ be a nonzero natural number and write $\bar{\mathbb{Q}}$ for `AlgebraicClosure ℚ`. The field [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111) is the intermediate field of $\bar{\mathbb{Q}}$-Laurent series generated over $\bar{\mathbb{Q}}$ by the coefficientwise image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305), the subfield of $\mathrm{LaurentSeries}\,\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ the family `divisorExpansions N`. Let $\sigma$ be a $\bar{\mathbb{Q}}$-algebra automorphism of this field, subject to the following interchange hypothesis: for all nonzero naturals $a,b$ with $ab = N$ and every element $x$ of the field whose underlying Laurent series is $\mathrm{coeffEmb}(\mathrm{qExpand}_{\mathbb{Q}}\,a\,(\mathrm{jq}))$ — the base change to $\bar{\mathbb{Q}}$ of the $q$-expansion $\mathrm{jq} = q^{-1}\cdot(\text{integral power series})$ of $j$ with $q$ replaced by $q^{a}$, i.e. obtained by multiplying exponents by $a$ — the underlying Laurent series of $\sigma x$ is $\mathrm{coeffEmb}(\mathrm{qExpand}_{\mathbb{Q}}\,b\,(\mathrm{jq}))$. Let $\tau$ be a $\mathbb{Q}$-algebra automorphism of $\bar{\mathbb{Q}}$ and let $z$ be a point of [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the quotient of the degree-zero divisors of `modularFunctionFieldBar N` over $\bar{\mathbb{Q}}$ by the subgroup of principal divisors. Then $\tau \bullet (\mathrm{ofAlgAut}\,\sigma \bullet z) = \mathrm{ofAlgAut}\,\sigma \bullet (\tau \bullet z)$, where $\mathrm{ofAlgAut}\,\sigma$ is the semilinear automorphism given by the pair $(\sigma, \mathrm{id}_{\bar{\mathbb{Q}}})$ and $\tau$ acts through the arithmetic Galois action on the degree-zero class group.
--
--   This is the statement that a Fricke-type automorphism of $X_0(N)$, characterised by its effect on the $q$-expansion generators $j(q^a) \mapsto j(q^b)$ for $ab = N$, is defined over $\mathbb{Q}$ and hence induces an endomorphism of $J_0(N)$ commuting with the action of $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$. It is used in the construction of Galois- and Hecke-equivariant pairings on torsion of $J_0(N)$ and in the computation of Frobenius determinants on its rational Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_galois_smul_ofAlgAut_smul_of_fricke.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.galois_smul_ofAlgAut_smul_of_fricke (N : ℕ) [NeZero N]
    (σ : ModularCurve.modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] ModularCurve.modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : ModularCurve.modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ a ModularCurve.jq) →
          ((σ x : ModularCurve.modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ b ModularCurve.jq))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (z : ModularCurve.JZero N) :
    τ • (AlgebraicCurve.SemilinearAut.ofAlgAut σ • z) = AlgebraicCurve.SemilinearAut.ofAlgAut σ • (τ • z) := by sorry

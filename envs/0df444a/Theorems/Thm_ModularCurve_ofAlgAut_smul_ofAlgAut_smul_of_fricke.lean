-- Prove2me | Theorems.Thm_ModularCurve_ofAlgAut_smul_ofAlgAut_smul_of_fricke
-- name    : ModularCurve.ofAlgAut_smul_ofAlgAut_smul_of_fricke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/60b221e1-4053-5300-b2f0-5e0a407fae1a
-- title:
--   Involutivity of the Fricke automorphism on J₀(N)
-- statement:
--   Let $N$ be a nonzero natural number and write $\bar F_N$ for [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}}$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images, under the base-change map `coeffEmb` induced by $\mathbb{Q}\to\overline{\mathbb{Q}}$, of the elements of the field [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305) $\subseteq \mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions of level $N$. Let $\sigma$ be an automorphism of $\bar F_N$ over $\overline{\mathbb{Q}}$ with the following property: for all nonzero naturals $a,b$ with $ab=N$ and every $x\in\bar F_N$ whose underlying Laurent series is the coefficientwise image of `qExpand ℚ a jq` — the series `jq` (the $q$-expansion $q^{-1}\cdot(\text{power series }$ `jNumQ`$)$ of the modular invariant) with its exponents scaled by $a$, i.e. $j(q^a)$ — the underlying Laurent series of $\sigma x$ is the coefficientwise image of $j(q^b)$. Let $z$ be an element of [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the group of degree-zero divisors of $\bar F_N$ over $\overline{\mathbb{Q}}$ modulo principal divisors. Then the semilinear automorphism [`AlgebraicCurve.SemilinearAut.ofAlgAut σ`](def/AlgebraicCurve_BaseChangeGalois.html#L76), namely the pair consisting of $\sigma$ as a ring automorphism of $\bar F_N$ together with the identity on $\overline{\mathbb{Q}}$, acts on $z$ as an involution: applying it twice returns $z$.
--
--   This is the statement that the Fricke involution $w_N$, characterised by its effect $j(q^a)\mapsto j(q^b)$ on the generators attached to factorisations $ab=N$, induces an involution on the degree-zero divisor class group $J_0(N)$ of the modular curve. It is used downstream in the computation of the determinant of Frobenius in a basis of the rational Tate module of `JZero N`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ofAlgAut_smul_ofAlgAut_smul_of_fricke.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ofAlgAut_smul_ofAlgAut_smul_of_fricke (N : ℕ) [NeZero N]
    (σ : ModularCurve.modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] ModularCurve.modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : ModularCurve.modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ a ModularCurve.jq) →
          ((σ x : ModularCurve.modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ b ModularCurve.jq))
    (z : ModularCurve.JZero N) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • (AlgebraicCurve.SemilinearAut.ofAlgAut σ • z) = z := by sorry

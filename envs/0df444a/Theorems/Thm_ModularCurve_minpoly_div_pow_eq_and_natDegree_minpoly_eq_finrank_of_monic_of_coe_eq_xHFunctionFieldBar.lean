-- Prove2me | Theorems.Thm_ModularCurve_minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
-- name    : ModularCurve.minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/b9cf2634-0b6d-5596-80c2-1666683eb54a
-- title:
--   Minimal polynomial of j(qᵖ)/jᵖ over the lower level field
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial, with $M/p$ nonzero; write $H' =$ `infSubgroup p M H hpM` for the image of $H$ under that reduction. Consider the two intermediate fields $E' =$ `xHFunctionFieldBar (M/p) H'` and $E =$ `xHFunctionFieldBar M H` of $\overline{\mathbb{Q}}$ inside the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, each obtained by adjoining to $\overline{\mathbb{Q}}$ the image of the corresponding rational $q$-expansion function field under the coefficientwise embedding. Let $\alpha\colon E' \to E$ be a $\overline{\mathbb{Q}}$-algebra homomorphism which acts as the identity on underlying Laurent series, i.e. the Laurent series of $\alpha(u)$ equals that of $u$ for all $u \in E'$. Let $x_0 \in E'$ have Laurent series `jqModC` (the $q$-expansion $q^{-1}\cdot(\text{power series }\mathrm{jNum})$ of the modular invariant) and let $x' \in E$ have Laurent series $q \mapsto q^p$ applied to `jqModC`, i.e. $j(q^p)$. Finally let $P \in E'[T]$ be monic with $\deg P = p+1$ and $P(x'/\alpha(x_0)^p) = 0$, the coefficients being mapped into $E$ by $\alpha$. Then, for the $E'$-algebra structure on $E$ induced by $\alpha$, the minimal polynomial of $x'/\alpha(x_0)^p$ over $E'$ equals $P$, and its degree equals `finrankAlong`, the $E'$-dimension of $E$ along $\alpha$.
--
--   This identifies, along the degeneracy inclusion of $q$-expansion function fields at a prime exactly dividing the level, the element $t_\infty = j(q^p)/j(q)^p$ as a generator whose minimal polynomial is any monic annihilating polynomial of degree $p+1$; the extension has degree $p+1$. It is used in the construction of étale charts at the cusps for the mod-$p$ model of $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx₀ : (x₀ : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x' : ↥(xHFunctionFieldBar M H))
    (hx' : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      (x' : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)))
    (P : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hPm : P.Monic) (hPd : P.natDegree = p + 1)
    (hPt : P.eval₂ α.toRingHom (x' / (α x₀) ^ p) = 0) :
    @minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) _ _
        (AlgebraicCurve.algebraAlong α) (x' / (α x₀) ^ p) = P ∧
      (@minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) _ _
        (AlgebraicCurve.algebraAlong α) (x' / (α x₀) ^ p)).natDegree = AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) α := by sorry

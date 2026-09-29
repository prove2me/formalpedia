-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem
-- name    : ModularCurve.finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/d0189c0e-8988-5ae4-b84d-b37b8a850624
-- title:
--   Degree ℓ+1 for a twist-fixed Laurent series
-- statement:
--   Let $\kappa$ be a field and $\ell$ a prime, and let $\zeta \in \kappa^{\times}$ be a unit whose image in $\kappa$ is a primitive $\ell$-th root of unity. For a unit $u$, write $\sigma_u =$ [`ModularCurve.qTwist`](def/ModularCurve_PhiGen.html#L35) $u$ for the ring endomorphism of the Laurent series field $\kappa((q)) =$ `LaurentSeries κ` that multiplies the coefficient of $q^{k}$ by $u^{k}$ for every $k \in \mathbb{Z}$, i.e. the substitution $f(q) \mapsto f(uq)$. Let $F$ be an intermediate field of $\kappa \subseteq \kappa((q))$ all of whose elements are fixed by $\sigma_{\zeta}$, and let $x, y \in \kappa((q))$ satisfy $\sigma_{\zeta} y \neq y$, $\sigma_{\zeta} x = x$ and $x \notin F$. Suppose there is a polynomial $P \in F[X]$ whose image under the coefficientwise map $F[X] \to \kappa((q))[X]$ factors as $$\prod_{k=0}^{\ell-1}\bigl(X - \sigma_{\zeta^{k}} y\bigr)\cdot (X - x).$$ Then the intermediate field $F(x)$ obtained by adjoining $x$ to $F$ inside $\kappa((q))$ satisfies $[F(x):F] = \ell + 1$.
--
--   A Kummer-theoretic degree computation for the twisting action $q \mapsto \zeta q$ on $\kappa((q))$: a twist-fixed element not already in the fixed field $F$, annihilated by a polynomial whose remaining roots form a single free twist-orbit of length $\ell$, generates an extension of degree exactly $\ell+1$. It is applied in [`ModularCurve.finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq`](thm.html#ModularCurve.finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq) to compute a degree of a $q$-expansion field over an Igusa-curve function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve Polynomial

universe u

theorem ModularCurve.finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem
    (κ : Type u) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] (ζ : κˣ) (hζ : IsPrimitiveRoot (ζ : κ) ℓ)
    (F : IntermediateField κ (LaurentSeries κ))
    (hF : ∀ f : LaurentSeries κ, f ∈ F → ModularCurve.qTwist ζ f = f)
    (x y : LaurentSeries κ) (hy : ModularCurve.qTwist ζ y ≠ y) (hxσ : ModularCurve.qTwist ζ x = x) (hx : x ∉ F)
    (P : Polynomial ↥F)
    (hP : P.map (algebraMap ↥F (LaurentSeries κ)) =
      (∏ k ∈ Finset.range ℓ, (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ k) y))) *
        (Polynomial.X - Polynomial.C x)) :
    Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = ℓ + 1 := by sorry

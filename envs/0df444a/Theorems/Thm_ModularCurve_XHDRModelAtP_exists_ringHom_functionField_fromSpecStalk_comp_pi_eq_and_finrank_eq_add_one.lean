-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one
-- name    : ModularCurve.XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4563e063-9ebb-5d68-a7e6-080db3a560bc
-- title:
--   Function-field map of π has degree p+1
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ but $p^2 \nmid M$, and with $M/p$ nonzero, together with a subgroup $H \le (\mathbb Z/M)^\times$ assumed to contain the whole kernel of the reduction map $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$, i.e. every unit $u$ with $\mathrm{unitsMap}(u) = 1$ lies in $H$. Assume the Laurent series $\mathrm{jqModC}\ \mathbb Q = q^{-1}\cdot \mathrm{jNum}$, the normalised $q$-expansion of $j$, lies in $\mathrm{qExpFunctionFieldC}\ \mathbb Q\ \top$, the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by quotients of integral $q$-expansions of modular forms of level one, and let $\mathfrak X$ be a datum of type `XHDRModelAtP p M H hpM hj`, the bundled $\mathbb Z_{(p)}$-model package at level $H$ and $p \parallel M$. Assume further that the two integral models `X p (ΓM M H) hj` and `X p (ΓN p M H hpM) hj`, attached to the levels `ΓM M H` and `ΓN p M H hpM`, are integral schemes. Then there is a ring homomorphism $\varphi$ from the function field of `X p (ΓN p M H hpM) hj` to that of `X p (ΓM M H) hj` such that: the canonical morphism from the spectrum of the stalk at the generic point of `X p (ΓM M H) hj`, followed by the scheme morphism $\mathfrak X.\pi.1$, equals $\mathrm{Spec}(\varphi)$ followed by the corresponding morphism for `X p (ΓN p M H hpM) hj`; $\varphi$ is a finite ring homomorphism; and, regarding the larger function field as an algebra over the smaller via $\varphi$, its rank as a module equals $p+1$.
--
--   This records the classical degree computation for the forgetful map between modular curves of level $H \subseteq (\mathbb Z/M)^\times$ and its image level modulo $M/p$, in the form of the induced extension of function fields of the two integral $\mathbb Z_{(p)}$-models together with the compatibility of that extension with the morphism $\pi$ at the generic point. It is the input, in the shape required by the flat-rank comparison, for [`ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi`](thm.html#ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi), which transfers the value $p+1$ to the fibre rank of $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsIntegral (X p (ΓM M H) hj)] [IsIntegral (X p (ΓN p M H hpM) hj)] :
    ∃ φ : (X p (ΓN p M H hpM) hj).functionField →+* (X p (ΓM M H) hj).functionField,
      (X p (ΓM M H) hj).fromSpecStalk (genericPoint (X p (ΓM M H) hj)) ≫ 𝔛.π.1 =
        Spec.map (CommRingCat.ofHom φ) ≫ (X p (ΓN p M H hpM) hj).fromSpecStalk (genericPoint (X p (ΓN p M H hpM) hj)) ∧
      φ.Finite ∧
      (letI := φ.toAlgebra; Module.finrank (X p (ΓN p M H hpM) hj).functionField (X p (ΓM M H) hj).functionField) = p + 1 := by sorry

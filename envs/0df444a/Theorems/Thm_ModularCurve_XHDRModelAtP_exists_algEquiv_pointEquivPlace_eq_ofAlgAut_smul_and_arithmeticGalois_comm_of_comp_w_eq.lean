-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq
-- name    : ModularCurve.XHDRModelAtP.exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/cfe242ef-9859-5a68-baf6-4639d6554ab7
-- title:
--   Atkin–Lehner automorphism on the geometric function field of X_H(M)
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral-form ratios for $\mathrm{SL}(2,\mathbb{Z})$; let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which packages a two-chart integral model of $X_H(M)$ over $R(p)$ together with a curve model $\mathfrak{X}.\mathrm{Meta}$ of $F :=$ `xHFunctionFieldBar M H` (the compositum of $\overline{\mathbb{Q}}$ with the $\mathbb{Q}$-rational function field of $X_H(M)$ inside $\overline{\mathbb{Q}}((q))$) over $\overline{\mathbb{Q}}$, an isomorphism `eeta` of $\mathfrak{X}.\mathrm{Meta}.C$ with the geometric generic fibre, and an isomorphism `𝔛.w` of the integral model. Then there is a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$ with two properties. First, for any two $\overline{\mathbb{Q}}$-points $y,y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ (morphisms $\mathrm{Spec}\,\overline{\mathbb{Q}} \to \mathfrak{X}.\mathrm{Meta}.C$ splitting $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$): if the image of $y'$ in the integral model under `eeta` followed by the first pullback projection and then by `𝔛.w.hom` coincides with the image of $y$ under `eeta` followed by that projection, then the place of $F$ attached to $y'$ by the bijection `pointEquivPlace` (between $\overline{\mathbb{Q}}$-points and places, a place being a valuation subring of $F$ other than $F$ itself, containing $\overline{\mathbb{Q}}$ and a principal ideal ring) is the translate of the place attached to $y$ under the semilinear automorphism `SemilinearAut.ofAlgAut θ`, i.e. the pair $(\theta, \mathrm{id}_{\overline{\mathbb{Q}}})$ acting by transport of valuation subrings. Second, $\theta$ commutes with the arithmetic Galois action: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $f \in F$, one has $\theta(\mathrm{arithmeticGalois}(\sigma) \cdot f) = \mathrm{arithmeticGalois}(\sigma) \cdot \theta(f)$, where `arithmeticGalois` sends $\sigma$ to the semilinear automorphism acting coefficientwise on Laurent series.
--
--   This records that the Atkin–Lehner-type automorphism $w$ carried by a Deligne–Rapoport-style model of $X_H(M)$ at $p \mid M$ induces, by pullback of functions, a $\overline{\mathbb{Q}}$-algebra automorphism $\theta = w^*$ of the geometric function field, described through its action on places and compatible with the arithmetic Galois action on $q$-expansion coefficients. It is used in the subsequent analysis of the Néron model and component group of the Jacobian $J_H$ at $p$, where the automorphism must be available simultaneously on functions, places and Galois translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_and_arithmeticGalois_comm_of_comp_w_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∃ θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H),

      (∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
        θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
          arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f) := by sorry

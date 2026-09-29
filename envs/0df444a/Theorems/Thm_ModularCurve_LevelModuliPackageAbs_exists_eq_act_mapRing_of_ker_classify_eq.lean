-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq
-- name    : ModularCurve.LevelModuliPackageAbs.exists_eq_act_mapRing_of_ker_classify_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/6797d969-39ea-5add-a499-e39070bc7dc5
-- title:
--   Equal classifying kernels yield a common model
-- statement:
--   Let $A$ be a commutative ring and let $Rd$ be rigid Weierstrass data over $A$: an assignment $T \mapsto Rd.\mathrm{Raw}\,T$ on commutative $A$-algebras, each raw datum $x$ carrying a Weierstrass curve $Rd.\mathrm{curve}\,x$ with unit discriminant, together with functorial base change $Rd.\mathrm{mapRing}$ along $A$-algebra maps and a compatible action $Rd.\mathrm{act}$ of the group of Weierstrass variable changes; $Rd.\mathrm{Pt}\,T$ is the associated quotient of $Rd.\mathrm{Raw}\,T$, whose elements are written $\mathrm{Quot.mk}$ of a raw datum, and $Rd.\mathrm{toLevelModuliDatum}$ packages these as a moduli datum with $j$-invariant $Rd.\mathrm{jOf}$. Let $P_0$ be an absolute level moduli package for it, i.e. a commutative $A$-algebra $B_0$ together with a point $P_0.\mathrm{univ} \in \mathrm{Pt}(B_0)$ such that for every $A$-algebra $T$ and every $x \in \mathrm{Pt}(T)$ there is a unique $A$-algebra map $\varphi : B_0 \to T$ with $\varphi_* P_0.\mathrm{univ} = x$; $P_0.\mathrm{classify}\,x$ denotes this $\varphi$. Let $K$ be a commutative $A$-algebra, let $x_1, x_2 \in \mathrm{Pt}(K)$ have $\ker(P_0.\mathrm{classify}\,x_1) = \ker(P_0.\mathrm{classify}\,x_2)$ as ideals of $B_0$, and let $y_1, y_2 \in Rd.\mathrm{Raw}\,K$ be raw data whose classes are $x_1$ and $x_2$. Write $R_0 \subseteq K$ for the image $A$-subalgebra of $P_0.\mathrm{classify}\,x_1$. Then there exist a raw datum $w \in Rd.\mathrm{Raw}\,R_0$, two injective $A$-algebra maps $\kappa_1, \kappa_2 : R_0 \to K$ with $\kappa_1$ the inclusion, and variable changes $C_1, C_2$ over $K$, such that $y_1 = Rd.\mathrm{act}\,C_1\,(Rd.\mathrm{mapRing}\,\kappa_1\,w)$ and $y_2 = Rd.\mathrm{act}\,C_2\,(Rd.\mathrm{mapRing}\,\kappa_2\,w)$.
--
--   This is the descent step saying that two points of the representable moduli problem whose classifying maps $B_0 \to K$ have the same kernel are base changes, along two embeddings of the common image ring, of a single raw Weierstrass datum over that ring, up to variable change over $K$. It is the level-structure-independent engine behind the comparisons of Weil pairing values for points with equal classifying kernels, in both the Katz and the Drinfeld variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.exists_eq_act_mapRing_of_ker_classify_eq
    (A : Type) [CommRing A] (Rd : ModularCurve.RigidWeierstrassData A)
    (P₀ : LevelModuliPackageAbs A Rd.toLevelModuliDatum)
    (K : Type) [CommRing K] [Algebra A K]
    (x₁ x₂ : Rd.toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : Rd.Raw K)
    (hy₁ : (Quot.mk _ y₁ : Rd.Pt K) = x₁) (hy₂ : (Quot.mk _ y₂ : Rd.Pt K) = x₂) :
    ∃ (w : Rd.Raw ↥(P₀.classify x₁).range) (κ₁ κ₂ : ↥(P₀.classify x₁).range →ₐ[A] K)
      (C₁ C₂ : WeierstrassCurve.VariableChange K),
      Function.Injective κ₁ ∧ Function.Injective κ₂ ∧ (∀ r : ↥(P₀.classify x₁).range, κ₁ r = (r : K)) ∧
      y₁ = Rd.act C₁ (Rd.mapRing κ₁ w) ∧ y₂ = Rd.act C₂ (Rd.mapRing κ₂ w) := by sorry

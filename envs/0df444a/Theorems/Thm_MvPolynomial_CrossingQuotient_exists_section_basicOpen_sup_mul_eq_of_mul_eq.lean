-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_exists_section_basicOpen_sup_mul_eq_of_mul_eq
-- name    : MvPolynomial.CrossingQuotient.exists_section_basicOpen_sup_mul_eq_of_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/f0b0c165-7d8f-5780-8700-6b98b5b501c1
-- title:
--   Glued quotient a_w/a = b_w/b on the crossing model uv = t
-- statement:
--   Let $W$ be a commutative ring, let $t, x', y' \in W$ satisfy $x' y' = t$, and let $w \in W^\times$. Put $Q = \mathrm{MvPolynomial}(\mathrm{Fin}\ 2, W)/(X_0 X_1 - t)$, the ring `CrossingQuotient W t`, and let $M = \operatorname{Spec} Q$ as a scheme; global sections of $M$ are identified with $Q$ by the inverse $\varphi$ of the canonical isomorphism $\Gamma(M,\top) \cong Q$. Writing $u$ and $v$ for the two distinguished coordinate elements `CrossingQuotient.U t` and `CrossingQuotient.V t` of $Q$, set $a = \varphi(u - x')$, $b = \varphi(y' - v)$, $a_w = \varphi(u - w x')$ and $b_w = \varphi(y' - w v)$, the images of $x', y', w$ in $Q$ being taken along the structure map from $W$. The assertion is that there exists a section $g \in \Gamma(M, D(a) \cup D(b))$ over the union of the two basic open sets of $a$ and $b$ such that the restriction of $g$ to $D(a)$ times the restriction of $a$ to $D(a)$ equals the restriction of $a_w$, the restriction of $g$ to $D(b)$ times the restriction of $b$ equals the restriction of $b_w$, and the restriction of $g$ to $(D(a) \cup D(b)) \cap (D(a_w) \cup D(b_w))$ is a unit in the ring of sections over that open set.
--
--   This is the local model computation at an ordinary double point: on the crossing $uv = x'y'$ the two ratios $(u - wx')/(u - x')$ and $(y' - wv)/(y' - v)$ agree where both are defined and glue to a single regular function off the section cut out by $a$ and $b$, invertible where the $w$-translated section is avoided. It is used as the transition datum in the crossing case of the inertia computations for models of modular curves, being cited by [`ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter`](thm.html#ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter) and by [`ModularCurve.XOneP.exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_exists_section_basicOpen_sup_mul_eq_of_mul_eq.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

theorem MvPolynomial.CrossingQuotient.exists_section_basicOpen_sup_mul_eq_of_mul_eq
    (W : Type u) [CommRing W] (t x' y' : W) (hxy : x' * y' = t) (w : Wˣ) :
    letI M : Scheme.{u} := Spec (CommRingCat.of (CrossingQuotient W t))
    letI φ : CrossingQuotient W t →+* Γ(M, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
    letI a : Γ(M, ⊤) := φ (CrossingQuotient.U t - algebraMap W _ x')
    letI b : Γ(M, ⊤) := φ (algebraMap W _ y' - CrossingQuotient.V t)
    letI aw : Γ(M, ⊤) := φ (CrossingQuotient.U t - algebraMap W _ ((w : W) * x'))
    letI bw : Γ(M, ⊤) := φ (algebraMap W _ y' - algebraMap W _ (w : W) * CrossingQuotient.V t)
    ∃ g : Γ(M, M.basicOpen a ⊔ M.basicOpen b),

      M.presheaf.map (homOfLE (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b)).op g *
          M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op a =
        M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op aw ∧

      M.presheaf.map (homOfLE (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b)).op g *
          M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op b =
        M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op bw ∧

      IsUnit (M.presheaf.map (homOfLE (inf_le_left :
          (M.basicOpen a ⊔ M.basicOpen b) ⊓ (M.basicOpen aw ⊔ M.basicOpen bw) ≤ M.basicOpen a ⊔ M.basicOpen b)).op g) := by sorry

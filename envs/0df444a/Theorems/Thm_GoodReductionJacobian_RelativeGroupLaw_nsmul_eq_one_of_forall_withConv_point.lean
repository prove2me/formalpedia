-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point
-- name    : GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_forall_withConv_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/9fcca341-6a4c-57c6-b7f1-4bbe7256fac5
-- title:
--   Exponent-m convolution character points give m-torsion sections
-- statement:
--   Let $R$ be a commutative domain, $K$ a fraction field of $R$ and $\bar K$ an algebraic closure of $K$, regarded as an $R$-algebra compatibly with $K$. Let $g_X \colon X \to \operatorname{Spec} R$ be a separated morphism of schemes and let $L$ be a relative group law on $g_X$, i.e. operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the sets $\{\varphi \colon T \to X \mid \varphi \text{ followed by } g_X = t\}$ for every $t \colon T \to \operatorname{Spec} R$, satisfying associativity, both unit laws, left inverses, and naturality of $\mathrm{mul}$ under precomposition with morphisms over $\operatorname{Spec} R$. Let $H$ be a commutative $R$-bialgebra such that $\operatorname{Spec} H$ is reduced and $\operatorname{Spec} H \to \operatorname{Spec} R$ is flat and locally of finite type, and let $u \colon \operatorname{Spec} H \to X$ satisfy $u$ followed by $g_X$ equals $\operatorname{Spec}$ of the structure map $R \to H$. For $\chi$ in the convolution monoid `WithConv (H →ₐ[R] Kbar)` write $u(\chi)$ for $\operatorname{Spec}(\chi)$ followed by $u$, a $\bar K$-point of $X$ over $\operatorname{Spec} R$. Assume $u(1) = L.\mathrm{one}$ and $u(\chi \chi') = L.\mathrm{mul}\,(u(\chi))\,(u(\chi'))$ for all $\chi, \chi'$, and that $\chi^m = 1$ for every $\chi$, where $m \in \mathbb{N}$. Then $L.\mathrm{nsmul}$ at $m$ applied to $u$ — the $m$-fold $L.\mathrm{mul}$-product of $u$ with itself, starting from $L.\mathrm{one}$ — equals $L.\mathrm{one}$.
--
--   This is the statement that an $H$-valued point of a separated group object which is multiplicative on $\bar K$-valued characters and whose character monoid has exponent dividing $m$ is killed by $[m]$; it is the mechanism by which a point coming from a group algebra of an $m$-torsion group is recognised as a section of the $m$-torsion subgroup. It is used in the construction of Néron-model objects for the modular curves $J_0$ and $J_H$ at a prime, where the relevant point is built from a multiplicative-type group scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_forall_withConv_point
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar] [IsScalarTower R K Kbar]
    {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} [IsSeparated gX] (L : RelativeGroupLaw R gX)
    (H : Type u) [CommRing H] [Bialgebra R H]
    [IsReduced (Spec (CommRingCat.of H))] [Flat (Spec.map (CommRingCat.ofHom (algebraMap R H)))]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R H)))]
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R H))) gX)
    (hone : (⟨Spec.map (CommRingCat.ofHom (1 : WithConv (H →ₐ[R] Kbar)).ofConv.toRingHom) ≫ u.1, by
        rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2; exact (1 : WithConv (H →ₐ[R] Kbar)).ofConv.comp_algebraMap⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gX) = L.one _)
    (hmul : ∀ χ χ' : WithConv (H →ₐ[R] Kbar),
      (⟨Spec.map (CommRingCat.ofHom (χ * χ').ofConv.toRingHom) ≫ u.1, by
          rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2; exact (χ * χ').ofConv.comp_algebraMap⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gX) =
        L.mul _
          ⟨Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ u.1, by
            rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 2; exact χ.ofConv.comp_algebraMap⟩
          ⟨Spec.map (CommRingCat.ofHom χ'.ofConv.toRingHom) ≫ u.1, by
            rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 2; exact χ'.ofConv.comp_algebraMap⟩)
    (m : ℕ) (htors : ∀ χ : WithConv (H →ₐ[R] Kbar), χ ^ m = 1) :
    L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R H))) m u = L.one _ := by sorry

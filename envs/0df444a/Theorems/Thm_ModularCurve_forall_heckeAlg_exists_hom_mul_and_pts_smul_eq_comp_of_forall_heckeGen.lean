-- Prove2me | Theorems.Thm_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen
-- name    : ModularCurve.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/8e788462-19a9-5c55-bb66-355d84dc7d1e
-- title:
--   From generators T_ℓ to the whole Hecke algebra
-- statement:
--   Let $R$ be a commutative ring with a ring map $R \to \overline{\mathbf Q}$, let $N \ge 1$, and let $g \colon G \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$ carrying a relative group law $L$: functorial multiplication, unit and inversion operations on the sets $\{\varphi \colon T \to G \mid \varphi \text{ followed by } g \text{ equals } s\}$ of $T$-points over each $s \colon T \to \operatorname{Spec} R$, satisfying the group axioms and compatible with base change along $T' \to T$; assume $L$ is commutative. Let $\mathrm{pts}$ be a bijection from $J := \operatorname{Pic}^0$ of the base-changed modular function field $\overline{\mathbf Q}\cdot F_N$ (degree-zero divisor classes) onto the set of $\overline{\mathbf Q}$-points of $G$ over $\operatorname{Spec}\overline{\mathbf Q} \to \operatorname{Spec} R$, carrying addition to $L$-multiplication. Give $J$ the $\mathbf T := \mathbf Z[X_\ell : \ell \text{ prime}]$-module structure `heckeModuleBar N`. Call $t \in \mathbf T$ realised if there is $\varphi \colon G \to G$ over $\operatorname{Spec} R$ whose post-composition action on $T$-points is an $L$-homomorphism for every $T$ and every $s \colon T \to \operatorname{Spec} R$, with $\mathrm{pts}(t \cdot x) = \mathrm{pts}(x)$ followed by $\varphi$ for all $x \in J$. The assertion: if every variable $X_\ell$ is realised, then every $t \in \mathbf T$ is realised.
--
--   This is the ring-theoretic closure step which upgrades a realisation of the individual Hecke operators $T_\ell$ as group endomorphisms of a relative group scheme to a realisation of the entire Hecke algebra, here presented as the free commutative ring $\mathbf Z[X_\ell]$ on the primes. It is used in assembling the Hecke action on a Néron model/good-reduction package for $J_0(N)$, where the action must be available for arbitrary Hecke algebra elements rather than just the generators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen
    (R : Type) [CommRing R] [Algebra R (AlgebraicClosure ℚ)] (N : ℕ) [NeZero N]
    {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g) (hcomm : L.IsCommutative)
    (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero N, pts (x + y) = L.mul _ (pts x) (pts y))
    (hgen : letI := heckeModuleBar N
      ∀ ℓ : Nat.Primes, ∃ φ : SchemeHomOver g g,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
        ∀ x : JZero N, (pts (heckeGen ℓ • x)).1 = (pts x).1 ≫ φ.1) :
    letI := heckeModuleBar N
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver g g,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero N, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by sorry

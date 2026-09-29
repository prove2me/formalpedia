-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/2633f268-362d-5d80-a579-121cfeda7caf
-- title:
--   Chevalley decomposition of a non-proper commutative group scheme
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a scheme whose underlying space is connected, and $f \colon G \to \operatorname{Spec} k$ a separated, quasi-compact morphism that is smooth of relative dimension $g$, equipped with a relative group law $L$ over $k$ — that is, for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the set of $k$-morphisms $T \to G$ over $t$, natural in $T$ — which is assumed commutative; assume further that $f$ is not proper. Then there exist a scheme $N$, a morphism $i \colon N \to G$, a relative group law $LN$ on $i \circ f$ (in diagrammatic order $i \gg f$), a natural number $h$, a scheme $A$ with a morphism $fA \colon A \to \operatorname{Spec} k$ carrying a relative group law $LA$, a natural number $a$, and a morphism $q \colon G \to A$ with $q$ followed by $fA$ equal to $f$, such that: $i$ is a closed immersion, $N$ is affine with connected underlying space, $i$ followed by $f$ is smooth of relative dimension $h$, $LN$ is commutative and $i$ is a homomorphism (post-composition with $i$ carries $LN$-products of $T$-points to $L$-products); $fA$ satisfies `AbelianSchemePropertyBundle`, i.e. it is smooth, proper, each fibre of its underlying map over a point of $\operatorname{Spec} k$ is connected, and it admits some relative group law; $fA$ is smooth of relative dimension $a$; $LA$ is commutative; $q$ is a homomorphism (post-composition with $q$ takes $L$-products to $LA$-products); the underlying map of $q$ is surjective; for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ and every $T$-point $x$ of $G$ over $t$, the composite of $x$ with $q$ is the $LA$-unit at $t$ if and only if $x$ factors through $i$; and finally $g = h + a$ with $1 \le h$.
--
--   This is Chevalley's structure theorem in the commutative case over an algebraically closed field, in the shape in which it is used here: a connected commutative algebraic group that is not proper is an extension of an abelian variety by a connected affine closed subgroup of positive dimension, with dimensions adding up. It is invoked in the dichotomy [`GoodReductionJacobian.RelativeGroupLaw.isProper_or_natCard_isTorsionPoint_le_pow_sub_one`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isProper_or_natCard_isTorsionPoint_le_pow_sub_one), where the positive-dimensional affine part is used to bound torsion when properness fails.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f] (hG : ¬ IsProper f) :
    ∃ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) (h : ℕ)
      (A : Scheme.{u}) (fA : A ⟶ Spec (CommRingCat.of k)) (LA : RelativeGroupLaw k fA) (a : ℕ)
      (q : SchemeHomOver f fA),
      IsClosedImmersion i ∧ IsAffine N ∧ ConnectedSpace N ∧ SmoothOfRelativeDimension h (i ≫ f) ∧
      LN.IsCommutative ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      AbelianSchemePropertyBundle k fA ∧ SmoothOfRelativeDimension a fA ∧ LA.IsCommutative ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
          LA.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q)) ∧
      Surjective q.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x q = LA.one t ↔
          ∃ y : SchemeHomOver t (i ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) ∧
      g = h + a ∧ 1 ≤ h := by sorry

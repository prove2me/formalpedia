-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isProper_of_forall_isAffine_isClosedImmersion_eq_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.isProper_of_forall_isAffine_isClosedImmersion_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/27779019-5e03-5a40-ba36-31a6e4555f11
-- title:
--   Properness from absence of positive-dimensional affine subgroups
-- statement:
--   Let $k$ be an algebraically closed field and let $f \colon G \to \operatorname{Spec} k$ be a morphism of schemes which is separated and quasi-compact, with $G$ a connected topological space, and which is smooth of relative dimension $g$ for some $g \in \mathbb{N}$. Suppose $G$ carries a relative group law $L$ over $k$, that is, for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set $\{\varphi \colon T \to G \mid \varphi$ followed by $f$ equals $t\}$ satisfying associativity, the two unit laws and left inversion, and compatible with base change along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$; suppose further that $L$ is commutative, i.e. its multiplication on each such set is commutative. Assume: for every scheme $N$, every morphism $i \colon N \to G$, every relative group law $L_N$ on $i$ followed by $f$, and every $h \in \mathbb{N}$, if $i$ is a closed immersion, $N$ is affine and connected, $i$ followed by $f$ is smooth of relative dimension $h$, and post-composition with $i$ (viewed as a morphism over $\operatorname{Spec} k$) carries the multiplication of $L_N$ to that of $L$ on all $T$-points, then $h = 0$. The conclusion is that $f$ is proper.
--
--   This is the commutative case of the completeness criterion underlying the Barsotti–Chevalley–Rosenlicht structure theorem: a connected commutative algebraic group over an algebraically closed field with no positive-dimensional connected affine subgroup is an abelian variety. It feeds the analysis of connected commutative algebraic groups used for the criterion of Néron–Ogg–Shafarevich, and is cited when producing a positive-dimensional affine connected subgroup of a non-proper such group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isProper_of_forall_isAffine_isClosedImmersion_eq_zero.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.isProper_of_forall_isAffine_isClosedImmersion_eq_zero
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (hG : ∀ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) (h : ℕ),
      IsClosedImmersion i → IsAffine N → ConnectedSpace N → SmoothOfRelativeDimension h (i ≫ f) →
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) →
      h = 0) :
    IsProper f := by sorry

-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
-- name    : GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/c72435ba-e8e5-5a36-8c38-c08f680561f4
-- title:
--   Rosenlicht's dichotomy for non-proper connected group schemes
-- statement:
--   Let $k$ be an algebraically closed field and let $f \colon G \to \operatorname{Spec} k$ be a morphism of schemes which is separated and quasi-compact, with $G$ a connected topological space, and which is smooth of relative dimension $g$ for a natural number $g$. Let $L$ be a relative group law on $f$: for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set of $\varphi \colon T \to G$ with $\varphi \circ f = t$, satisfying associativity, the two unit laws and left inverse, and compatible with base change along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $f$ is not proper. Then either $G$ is affine, or there are a scheme $H$, a morphism $i \colon H \to G$, a relative group law $LH$ on $i$ followed by $f$, and a natural number $h$ such that $i$ is a closed immersion, $H$ is connected, $i$ followed by $f$ is smooth of relative dimension $h$, the morphism $i$ is a homomorphism on points (for every $t \colon T \to \operatorname{Spec} k$ and all $T$-points $x,y$ of $H$ over $t$, composing $LH.\mathrm{mul}\,t\,x\,y$ with $i$ equals $L.\mathrm{mul}$ of the composites of $x$ and of $y$ with $i$), and $1 \le h < g$.
--
--   This is the geometric half of Rosenlicht's proof of the Barsotti–Chevalley structure theorem: a connected smooth group scheme over an algebraically closed field that is not proper is either affine or contains a connected smooth closed subgroup of dimension strictly between $0$ and $\dim G$. It feeds the induction establishing that a connected group scheme all of whose connected smooth closed subgroups of positive dimension are non-affine, or absent, is proper.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_or_exists_isClosedImmersion_lt_of_not_isProper.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    (hG : ¬ IsProper f) :
    IsAffine G ∨
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)) (h : ℕ),
      IsClosedImmersion i ∧ ConnectedSpace H ∧ SmoothOfRelativeDimension h (i ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      1 ≤ h ∧ h < g := by sorry

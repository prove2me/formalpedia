-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/929a0b7a-86af-5a1e-b160-d0ccdb1dbe43
-- title:
--   Preimage of a connected affine closed subgroup under a smooth surjection
-- statement:
--   Let $k$ be a field and $f\colon G\to\operatorname{Spec}k$ a $k$-scheme equipped with a relative group law $L$, i.e. with multiplication, unit and inverse operations on the sets $\{\varphi\colon T\to G \mid \varphi\circ f=t\}$ of sections over each $k$-scheme $(T,t)$, satisfying associativity, the unit laws, left inversion, and naturality under base change. Let $i\colon N\to G$ be a closed immersion with $N$ affine and $i$ followed by $f$ geometrically connected; let $f_Q\colon Q\to\operatorname{Spec}k$ carry a relative group law $L_Q$, and let $q\colon G\to Q$ be a morphism with $q$ followed by $f_Q$ equal to $f$, which is surjective, quasi-compact and smooth of relative dimension $h$, is a homomorphism on $T$-valued sections for every $(T,t)$, and has kernel $N$ in the sense that $x$ followed by $q$ equals $L_Q.\mathrm{one}\,t$ exactly when $x$ factors through $i$. Let $j\colon M\to Q$ be a closed immersion with $M$ affine and connected, $j$ followed by $f_Q$ smooth of relative dimension $m$, carrying a relative group law $L_M$ for which $j$ is a homomorphism on sections. Then there exist a scheme $P$, a closed immersion $\iota\colon P\to G$ and a relative group law $L_P$ on $\iota$ followed by $f$, such that $P$ is affine and connected, $\iota$ followed by $f$ is smooth of relative dimension $h+m$, $\iota$ is a homomorphism on sections, and for every $(T,t)$ a section $x$ of $f$ factors through $\iota$ if and only if $x$ followed by $q$ factors through $j$.
--
--   This realises the preimage $q^{-1}(M)=G\times_Q M$ as a connected affine closed subgroup of $G$ of dimension $h+m$, the scheme-theoretic form of the statement that an extension of a connected affine group by a connected affine group is again connected and affine (SGA 3, Exp. VI$_B$, Prop. 9.2). It is used in the construction of the affine part of a group scheme without proper reduction, through [`GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] [IsAffine N] [GeometricallyConnected (i ≫ f)]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ) (h : ℕ) [SmoothOfRelativeDimension h q.1] [Surjective q.1]
    [QuasiCompact q.1]
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)
    {M : Scheme.{u}} (j : M ⟶ Q) [IsClosedImmersion j] [IsAffine M] [ConnectedSpace M]
    (LM : RelativeGroupLaw k (j ≫ fQ)) (m : ℕ) [SmoothOfRelativeDimension m (j ≫ fQ)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ fQ)),
      NeronModelInfra.schemeHomOverComp (LM.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))
          (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))) :
    ∃ (P : Scheme.{u}) (ι : P ⟶ G) (LP : RelativeGroupLaw k (ι ≫ f)),
      IsClosedImmersion ι ∧ IsAffine P ∧ ConnectedSpace P ∧
      SmoothOfRelativeDimension (h + m) (ι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (ι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LP.mul t x y) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        (∃ y : SchemeHomOver t (ι ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f) = x) ↔
          ∃ z : SchemeHomOver t (j ≫ fQ),
            NeronModelInfra.schemeHomOverComp z (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) =
              NeronModelInfra.schemeHomOverComp x q) := by sorry

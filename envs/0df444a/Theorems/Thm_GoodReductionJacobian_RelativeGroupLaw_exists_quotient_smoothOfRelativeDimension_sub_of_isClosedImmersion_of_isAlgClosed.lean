-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/eb9e2b12-3dee-5b73-b415-71aaf64e4c26
-- title:
--   Quotient of a smooth group scheme by a smooth normal subgroup
-- statement:
--   Let $k$ be an algebraically closed field, let $f\colon G\to\operatorname{Spec}k$ be a separated, quasi-compact morphism of schemes, and let $L$ be a relative group law for $f$: a group structure $(\mathrm{mul},\mathrm{one},\mathrm{inv})$ on the set of morphisms $T\to G$ over $\operatorname{Spec}k$, for every $k$-scheme $t\colon T\to\operatorname{Spec}k$, satisfying associativity, unit and left inverse laws and compatible with precomposition along any $\psi\colon T'\to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $f$ is smooth of relative dimension $g$. Let $i\colon N\to G$ be a closed immersion, let $L_N$ be a relative group law for $i$ followed by $f$, which is smooth of relative dimension $h$. Assume $i$ is a homomorphism, in the sense that for all $t$ and all $x,y$ over $t$ in $N$, composing $L_N.\mathrm{mul}\,t\,x\,y$ with $i$ equals $L.\mathrm{mul}$ of the composites of $x$ and $y$ with $i$; and assume normality: for all $t$, every $x$ over $t$ in $G$ and every $n$ over $t$ in $N$, there is $n'$ over $t$ in $N$ whose composite with $i$ equals $L.\mathrm{mul}\,t\,(L.\mathrm{mul}\,t\,x\,(n\text{ after }i))\,(L.\mathrm{inv}\,t\,x)$. Then there exist a scheme $Q$, a morphism $f_Q\colon Q\to\operatorname{Spec}k$, a relative group law $L_Q$ for $f_Q$, and a morphism $q\colon G\to Q$ with $q$ followed by $f_Q$ equal to $f$, such that $f_Q$ is separated and quasi-compact and smooth of relative dimension $g-h$ (truncated subtraction), $h\le g$, $q$ is smooth of relative dimension $h$ and surjective, $q$ is a homomorphism on $T$-valued points for every $k$-scheme $T$, $L_Q$ is commutative whenever $L$ is, and for every $t$ and every $x$ over $t$ in $G$ one has $x$ followed by $q$ equal to $L_Q.\mathrm{one}\,t$ if and only if $x$ factors as some $y$ over $t$ in $N$ followed by $i$.
--
--   This is the existence of the quotient $G/N$ of a smooth group scheme by a smooth normal closed subgroup scheme over an algebraically closed field, with the expected dimension count and with $N$ realised as the kernel of the quotient map on points. It is used in the scheme-theoretic input to the good-reduction theory of Jacobians, in particular in the structure-theoretic statements about proper and affine parts of such group schemes that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
      (n : SchemeHomOver t (i ≫ f)), ∃ n' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
            (L.inv t x)) :
    ∃ (Q : Scheme.{u}) (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
      (q : SchemeHomOver f fQ),
      IsSeparated fQ ∧ QuasiCompact fQ ∧ SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g ∧
      SmoothOfRelativeDimension h q.1 ∧ Surjective q.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
          LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q)) ∧
      (L.IsCommutative → LQ.IsCommutative) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
          ∃ y : SchemeHomOver t (i ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) := by sorry

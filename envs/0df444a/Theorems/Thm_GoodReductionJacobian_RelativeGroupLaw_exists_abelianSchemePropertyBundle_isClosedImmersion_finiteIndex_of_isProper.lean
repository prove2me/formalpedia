-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f120ab4a-b234-597e-b631-1f59cb00467c
-- title:
--   Abelian subvariety of finite index in a proper group scheme
-- statement:
--   Let $k$ be an algebraically closed field, let $N$ be a scheme with a structure morphism $gN \colon N \to \operatorname{Spec} k$ which is proper, and let $LN$ be a relative group law on $gN$: a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the set of sections $\{\varphi : T \to N \mid \varphi \text{ over } t\}$ for every $k$-scheme $t \colon T \to \operatorname{Spec} k$, natural in $T$ along base-changing morphisms. The assertion is the existence of a scheme $A$, a structure morphism $fA \colon A \to \operatorname{Spec} k$, a relative group law $LA$ on $fA$, a natural number $d$, and a morphism $\iota \colon A \to N$ with $\iota$ followed by $gN$ equal to $fA$, such that: $LA$ is commutative on $T$-points for every $T$; $fA$ is smooth, proper, has $\_$connected fibre over every point of $\operatorname{Spec} k$ and admits some relative group law; $fA$ is smooth of relative dimension $d$; $\iota$ is a closed immersion; $\iota$ is a homomorphism, i.e. composing $LA.\mathrm{mul}\,t\,x\,y$ with $\iota$ gives $LN.\mathrm{mul}\,t$ of the composites of $x$ and $y$ with $\iota$, for all $T$-points $x,y$ of $fA$; and the image of $A(k)$ has finite index in $N(k)$, in the sense that there is a finite set $S$ of sections of $gN$ over $\mathrm{id}_{\operatorname{Spec} k}$ such that every such section $x$ is $LN.\mathrm{mul}$ of some $s \in S$ with $\iota \circ a$ for some section $a$ of $fA$.
--
--   This is the passage from an arbitrary proper group scheme over an algebraically closed field to an abelian variety: one takes for $A$ the identity component of the reduced closed subscheme of $N$, which is a smooth proper connected commutative group scheme of some dimension $d$, closed in $N$ and of finite index on $k$-points. It is used in the study of torsion sections of $N$, namely by [`GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_isTorsionPoint_pow_schemeHomOverComp_eq`](thm.html#GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_isTorsionPoint_pow_schemeHomOverComp_eq) and by [`GoodReductionJacobian.RelativeGroupLaw.finite_setOf_schemeHomOverComp_eq_one_of_isProper_of_forall_isTorsionPoint`](thm.html#GoodReductionJacobian.RelativeGroupLaw.finite_setOf_schemeHomOverComp_eq_one_of_isProper_of_forall_isTorsionPoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}}
    {gN : N ⟶ Spec (CommRingCat.of k)} [IsProper gN] (LN : RelativeGroupLaw k gN) :
    ∃ (A : Scheme.{u}) (fA : A ⟶ Spec (CommRingCat.of k)) (LA : RelativeGroupLaw k fA) (d : ℕ)
      (ι : SchemeHomOver fA gN),
      LA.IsCommutative ∧ AbelianSchemePropertyBundle k fA ∧ SmoothOfRelativeDimension d fA ∧
      IsClosedImmersion ι.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t fA),
        NeronModelInfra.schemeHomOverComp (LA.mul t x y) ι =
          LN.mul t (NeronModelInfra.schemeHomOverComp x ι)
            (NeronModelInfra.schemeHomOverComp y ι)) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA,
            x = LN.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a ι) := by sorry

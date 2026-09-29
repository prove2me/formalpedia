-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/50c3bff3-4a5a-5d23-92fb-7cbfe6a937ad
-- title:
--   Rosenlicht decomposition for an abelian subvariety, commutative case
-- statement:
--   Let $k$ be an algebraically closed field and let $f \colon G \to \operatorname{Spec} k$ be a separated, quasi-compact morphism with $G$ a connected scheme, equipped with a relative group law $L$ over $k$, i.e. a group structure $(\mathrm{mul}, \mathrm{one}, \mathrm{inv})$ on the set $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of points of $G$ over each $k$-scheme $t \colon T \to \operatorname{Spec} k$, compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$; assume $L$ is commutative, and that $f$ is smooth of relative dimension $g$. Let $j \colon A \to G$ be a closed immersion with $A$ connected, with $j$ followed by $f$ proper and smooth of relative dimension $a$, and let $LA$ be a relative group law on $A$ over $k$ such that $j$ is a homomorphism on points: for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ and all $x, y$ in $A(T)$ over $t$, the composite of $LA.\mathrm{mul}\,t\,x\,y$ with $j$ equals $L.\mathrm{mul}$ of the composites of $x$ and of $y$ with $j$. The conclusion asserts the existence of a scheme $N$, a closed immersion $i \colon N \to G$ and a relative group law $LN$ on $N$ over $k$ such that $N$ is connected, $i$ followed by $f$ is smooth of relative dimension $g - a$ (truncated subtraction), $a \le g$, $i$ is a homomorphism on points in the same sense as $j$, and the multiplication morphism is surjective: on the fibre product $A \times_{\operatorname{Spec} k} N$ (the pullback of $j \circ f$ along $i \circ f$, with its structure map to $\operatorname{Spec} k$), the underlying morphism of the $L$-product of the first projection followed by $j$ and the second projection followed by $i$ is a surjective morphism to $G$.
--
--   This is Rosenlicht's decomposition theorem in the commutative case over an algebraically closed field: an abelian subvariety $A$ of a connected commutative algebraic group $G$ admits an almost-complement, here normalised to be a connected smooth closed subgroup scheme whose relative dimension is recorded as $g - a$ rather than phrasing the conclusion via finiteness of $A \cap N$. It is used in the analysis of properness of subgroup schemes, in particular by [`GoodReductionJacobian.RelativeGroupLaw.isProper_of_forall_isAffine_isClosedImmersion_eq_zero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isProper_of_forall_isAffine_isClosedImmersion_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {A : Scheme.{u}} (j : A ⟶ G) [IsClosedImmersion j] [ConnectedSpace A] [IsProper (j ≫ f)]
    (LA : RelativeGroupLaw k (j ≫ f)) (a : ℕ) [SmoothOfRelativeDimension a (j ≫ f)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ f)),
      NeronModelInfra.schemeHomOverComp (LA.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))) :
    ∃ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧ ConnectedSpace N ∧ SmoothOfRelativeDimension (g - a) (i ≫ f) ∧
      a ≤ g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      Surjective
        (L.mul (pullback.fst (j ≫ f) (i ≫ f) ≫ j ≫ f)
          ⟨pullback.fst (j ≫ f) (i ≫ f) ≫ j, Category.assoc _ _ _⟩
          ⟨pullback.snd (j ≫ f) (i ≫ f) ≫ i,
            (Category.assoc _ _ _).trans pullback.condition.symm⟩).1 := by sorry

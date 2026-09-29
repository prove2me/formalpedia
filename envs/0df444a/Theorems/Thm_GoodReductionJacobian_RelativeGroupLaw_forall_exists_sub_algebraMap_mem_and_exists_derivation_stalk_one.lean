-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/89987b7b-f99f-5afe-9e77-57c42b57d385
-- title:
--   Tangent vectors at the unit extend to derivations
-- statement:
--   Let $k$ be a field, let $G$ be a scheme (in the bottom universe) and let $g : G \to \operatorname{Spec} k$ be a morphism that is locally of finite type, and let $L$ be a relative group law for $g$: that is, for every scheme $T$ and every $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi : T \to G \mid \varphi \text{ followed by } g = t\}$, satisfying associativity, both unit laws and the left inverse law, together with compatibility of the multiplication with precomposition along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Write $e \in G$ for the image of the closed point of $\operatorname{Spec} k$ under the unit section $L.\mathrm{one}$ at $t = \mathrm{id}_{\operatorname{Spec} k}$, and give the local ring $A = \mathcal{O}_{G,e}$ the $k$-algebra structure obtained from the global sections map of $g$, the canonical identification $\Gamma(\operatorname{Spec} k) \cong k$ and the germ map at $e$. The theorem asserts two things. First, every $a \in A$ satisfies $a - c \in \mathfrak{m}_e$ for some $c \in k$, i.e. the residue field of $A$ is $k$. Second, for every $k$-linear functional $\varphi : A \to k$ vanishing on $\mathfrak{m}_e^2$ and on the image of $k$, there exists a $k$-derivation $D : A \to A$ with $D(a) - \varphi(a) \in \mathfrak{m}_e$ for all $a \in A$.
--
--   This is the construction of invariant derivations on a group scheme over a field: a tangent vector at the unit, presented as a functional on the local ring killing the square of the maximal ideal and the constants, is realised as the value at $e$ of a global derivation of $\mathcal{O}_{G,e}$, the $k$-rationality of $e$ being recorded alongside. It is used by [`GoodReductionJacobian.RelativeGroupLaw.isReduced_stalk_one_of_charZero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isReduced_stalk_one_of_charZero), where such derivations force reducedness of the local ring at the unit in characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one
    (k : Type) [Field k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    let e : ↥G := (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)
    letI : Algebra k (G.presheaf.stalk e) :=
      ((G.presheaf.germ ⊤ e trivial).hom.comp (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
    (∀ a : G.presheaf.stalk e, ∃ c : k, a - algebraMap k (G.presheaf.stalk e) c ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk e)) ∧
    ∀ φ : (G.presheaf.stalk e) →ₗ[k] k,
      (∀ a ∈ (IsLocalRing.maximalIdeal (G.presheaf.stalk e)) ^ 2, φ a = 0) →
      (∀ c : k, φ (algebraMap k (G.presheaf.stalk e) c) = 0) →
      ∃ D : Derivation k (G.presheaf.stalk e) (G.presheaf.stalk e),
        ∀ a : G.presheaf.stalk e, D a - algebraMap k (G.presheaf.stalk e) (φ a) ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk e) := by sorry

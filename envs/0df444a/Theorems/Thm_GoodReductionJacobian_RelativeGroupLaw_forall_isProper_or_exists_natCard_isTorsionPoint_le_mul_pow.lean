-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow
-- name    : GoodReductionJacobian.RelativeGroupLaw.forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/340388e8-fbc7-5d1f-ad57-11f99bdc7584
-- title:
--   Proper identity component, or O(m²ᵈ⁻¹) geometric m-torsion points
-- statement:
--   Let $k$ be a field and let $f \colon G \to \operatorname{Spec} k$ be a morphism of schemes that is separated, locally of finite type and quasi-compact, and smooth of relative dimension $d$ for a natural number $d$. Let $L$ be a `RelativeGroupLaw` for $f$, that is, for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ a group structure (multiplication, unit and inverse, associative, unital, with left inverses) on the set of morphisms $T \to G$ over $t$, the multiplication being natural in $T$ along morphisms $\psi$ with $\psi$ followed by $t$ equal to $t'$; assume $L$ is commutative, i.e. its multiplication is commutative on every such set. Let $k'$ be an algebraically closed field equipped with a $k$-algebra structure. Then at least one of the following holds. (1) For every scheme $G_0$ and every open immersion $i \colon G_0 \to G$ whose set-theoretic range is the connected component, in the space $G$, of the image of the closed point of $\operatorname{Spec} k$ under the unit section $L.\mathrm{one}$ of the identity of $\operatorname{Spec} k$, the composite $i$ followed by $f$ is proper. (2) $0 < d$ and there is a natural number $c$ such that for every $m \in \mathbb{N}$ whose image in $k$ is nonzero, the set of morphisms $\operatorname{Spec} k' \to G$ over the structure morphism $\operatorname{Spec} k' \to \operatorname{Spec} k$ whose $m$-fold $L$-sum (iterated multiplication starting from the unit) equals the unit is finite, of cardinality at most $c \cdot m^{2d-1}$.
--
--   This is Lemma 1 of Serre and Tate's paper on good reduction of abelian varieties, in the form consumed by the implication (b) $\Rightarrow$ (a) of their Theorem 1: a smooth commutative group scheme of relative dimension $d$ over a field either has proper identity component or has too few geometric points of order dividing $m$ for the torsion bound coming from an abelian variety. It is used in the construction of the abelian-scheme data attached to a Néron model whose geometric $m$-torsion is large.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'] :
    (∀ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) [IsOpenImmersion i],
        Set.range i =
          connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) →
        IsProper (i ≫ f)) ∨
    (0 < d ∧ ∃ c : ℕ, ∀ m : ℕ, (m : k) ≠ 0 →
        Finite {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f //
            L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap k k'))) m x} ∧
        Nat.card {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f //
            L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap k k'))) m x} ≤
          c * m ^ (2 * d - 1)) := by sorry

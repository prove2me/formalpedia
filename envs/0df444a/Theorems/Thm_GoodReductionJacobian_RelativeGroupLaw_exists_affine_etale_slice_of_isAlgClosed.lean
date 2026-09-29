-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_affine_etale_slice_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_affine_etale_slice_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b592792a-bcaf-54ff-9673-8f9f8040035d
-- title:
--   Affine étale slice for translation by a closed subgroup
-- statement:
--   Let $k$ be an algebraically closed field, let $G$ be a scheme and $f : G \to \operatorname{Spec} k$ a separated, quasi-compact morphism which is smooth of relative dimension $g$, and let $L$ be a relative group law for $f$: a group structure on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points of $G$ over $k$, for every $k$-scheme $(T,t)$, compatible with base change along morphisms $T' \to T$ over $k$. Let $i : N \to G$ be a closed immersion such that $i$ followed by $f$ is smooth of relative dimension $h$, equipped with a relative group law $L_N$, and assume that $i$ is a homomorphism on points: for every $k$-scheme $(T,t)$ and all $T$-points $x,y$ of $N$ over $k$, the composite of $L_N$-product of $x$ and $y$ with $i$ equals the $L$-product of the composites of $x$ and $y$ with $i$. Then there are a scheme $S$ and a morphism $j : S \to G$ such that $S$ is affine and has a point, $j$ followed by $f$ is smooth of relative dimension $g - h$ (truncated subtraction), and the composite of the canonical morphism $N \times_k S \to N \times_k G$ induced by $\mathrm{id}_N$ and $j$ with the action morphism `L.action i` — the first component of the $L$-product of the $N \times_k G$-point $i \circ \mathrm{pr}_1$ and the point $\mathrm{pr}_2$, i.e. $(n,x) \mapsto i(n)\cdot x$ — is étale.
--
--   This is the existence of an affine quasi-section, or étale slice, for the translation action of a smooth closed subgroup $N$ on a smooth group scheme $G$ over an algebraically closed field: the restriction of the multiplication $N \times_k S \to G$ to a suitable $(g-h)$-dimensional affine slice $S$ is étale. It is used in the construction of a saturated, faithfully flat quotient of $G$ by a closed subgroup scheme in the study of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_affine_etale_slice_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_affine_etale_slice_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    ∃ (S : Scheme.{u}) (j : S ⟶ G), IsAffine S ∧ Nonempty S ∧ SmoothOfRelativeDimension (g - h) (j ≫ f) ∧
      Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) := by sorry

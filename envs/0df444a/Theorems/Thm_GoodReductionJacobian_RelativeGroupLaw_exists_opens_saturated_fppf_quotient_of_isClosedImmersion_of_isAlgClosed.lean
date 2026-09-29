-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/efc042bf-fe67-5641-9905-fea1e48689ae
-- title:
--   Generic fppf quotient on a saturated open of G
-- statement:
--   Let $k$ be an algebraically closed field, let $f : G \to \operatorname{Spec} k$ be separated and quasi-compact and smooth of relative dimension $g$, and let $L$ be a relative group law for $f$: a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, and naturality of multiplication under base change of the test scheme) on the sets of $T$-points $\{\varphi : T \to G \mid \varphi \circ f = t\}$ for each $t : T \to \operatorname{Spec} k$. Let $i : N \to G$ be a closed immersion, let $L_N$ be a relative group law for $i$ followed by $f$, smooth of relative dimension $h$, and assume $i$ is a homomorphism in the sense that for every test base $t : T \to \operatorname{Spec} k$ and all points $x,y$ of $N$ over $t$, composing $L_N.\mathrm{mul}\,t\,x\,y$ with $i$ equals $L.\mathrm{mul}$ applied to the composites of $x$ and $y$ with $i$. Write $s = \mathrm{pr}_2 : N \times_{\operatorname{Spec} k} G \to G$ for the second projection of the pullback of $i$ followed by $f$ along $f$, and $a = L.\mathrm{action}\ i$ for the morphism $N \times_{\operatorname{Spec} k} G \to G$ obtained by multiplying the first projection pushed forward along $i$ with the second projection. Then there exist an open subscheme $U \subseteq G$ with $s^{-1}U = a^{-1}U$ such that $U$ is non-empty, and a scheme $Y$ together with a morphism $p : U \to Y$ such that the restriction $s|_U : s^{-1}U \to U$ and the restriction $a|_U$, precomposed with the isomorphism of open subschemes given by the saturation equality, become equal after composition with $p$, and such that $p$ is flat, locally of finite presentation, quasi-compact and surjective, and the square formed by these two restrictions and $p$, $p$ is a pullback square. No universal property of $p$ as a coequaliser is asserted.
--
--   This is the theorem on generic passage to the quotient by a flat groupoid, specialised to the translation action of a smooth closed subgroup scheme $N$ on a smooth group scheme $G$ over an algebraically closed field: on a suitable non-empty $N$-saturated open $U \subseteq G$ the equivalence relation is effective, with an fppf quotient map $p$ whose diagonal square is cartesian. It is used to produce the fppf quotient morphism fitting into a pullback square with the action, in the construction of quotients needed for the Jacobian with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    ∃ (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U),
      Nonempty (U.toScheme) ∧
      ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p := by sorry

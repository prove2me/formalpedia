-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_baseChange_baseChange_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/9dd46be7-7494-5643-bf38-c982fdc9d41b
-- title:
--   Iterated base change of a relative group law
-- statement:
--   Let $R$, $R'$, $R''$ be commutative rings in a fixed universe, let $\iota \colon \operatorname{Spec} R' \to \operatorname{Spec} R$ and $j \colon \operatorname{Spec} R'' \to \operatorname{Spec} R'$ be morphisms of schemes, let $A$ be a scheme with a morphism $f \colon A \to \operatorname{Spec} R$, and let $G$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points over each $t \colon T \to \operatorname{Spec} R$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverses, and compatibility with precomposition by morphisms over $\operatorname{Spec} R$. Writing the base change of $f$ along $\iota$ as the second projection $\operatorname{pullback.snd} f\,\iota$, the assertion is that there exist morphisms $u$ from the twice-base-changed scheme $(A \times_R R') \times_{R'} R''$ to $A \times_R R''$ and $v$ in the opposite direction, each commuting with the second projections to $\operatorname{Spec} R''$, such that: $u$ followed by $v$ and $v$ followed by $u$ are the respective identities; $u$ followed by $\operatorname{pullback.fst} f\,(j \circ \iota)$ equals $\operatorname{pullback.fst} (\operatorname{pullback.snd} f\,\iota)\, j$ followed by $\operatorname{pullback.fst} f\,\iota$; and for every scheme $T$, every $t \colon T \to \operatorname{Spec} R''$ and all $T$-points $x, y$ over $t$ of the twice-base-changed scheme, the product of $x$ and $y$ for the group law $(G_{\iota})_{j}$, followed by $u$, equals the product for the group law $G_{j \circ \iota}$ of $x$ followed by $u$ and of $y$ followed by $u$. (Only $u$ is asserted to be multiplicative; $v$ is produced merely as its two-sided inverse over $\operatorname{Spec} R''$.)
--
--   This is the statement that the canonical pasting isomorphism $(A \times_R R') \times_{R'} R'' \cong A \times_R R''$ identifies the iterated base change of a relative group law with the base change along the composite, in the form of an isomorphism over $\operatorname{Spec} R''$ that is compatible with the projections to $A$ and multiplicative on points. It is used to transport properties of multiplication-by-$n$ (finiteness, flatness, surjectivity) between successive base changes, and is cited in the treatment of split tori over henselian bases and in the analysis of $[n]$ on base changes of relative group laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_baseChange_baseChange_iso
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] {R'' : Type u} [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    ∃ (u : SchemeHomOver (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))
          (RelativeGroupLaw.baseChangeStr (j ≫ ι) f))
      (v : SchemeHomOver (RelativeGroupLaw.baseChangeStr (j ≫ ι) f)
          (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))),
      u.1 ≫ v.1 = 𝟙 _ ∧ v.1 ≫ u.1 = 𝟙 _ ∧
      u.1 ≫ pullback.fst f (j ≫ ι) = pullback.fst (pullback.snd f ι) j ≫ pullback.fst f ι ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
        (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))),
        NeronModelInfra.schemeHomOverComp (((G.baseChange ι).baseChange j).mul t x y) u =
          (G.baseChange (j ≫ ι)).mul t (NeronModelInfra.schemeHomOverComp x u)
            (NeronModelInfra.schemeHomOverComp y u) := by sorry

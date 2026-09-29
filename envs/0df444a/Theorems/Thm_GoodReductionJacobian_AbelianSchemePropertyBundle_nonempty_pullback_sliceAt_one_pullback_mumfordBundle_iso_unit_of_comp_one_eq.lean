-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/09a547d0-c59e-5784-828c-e953d6d64f4c
-- title:
--   Trivialisation of (u× v)^*Λ(L) on both unit slices
-- statement:
--   Let $B$ be a local commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$ a morphism, and let $L$ be a relative group law on $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} B$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverses and naturality of multiplication under base change. Assume $f$ carries the property bundle `AbelianSchemePropertyBundle` ($f$ smooth and proper, every fibre of the underlying map connected, and a relative group law existing), and let $\mathcal L$ be a module on $A$ which is invertible in the sense that each point has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit. Write $e := (L.\mathrm{one}\,(\mathbf 1))_1 : \operatorname{Spec} B \to A$ for the unit section. Let $u, v : A \to A$ satisfy $u$ followed by $f$ equals $f$, likewise for $v$, and fix the unit, $e$ followed by $u$ (resp. $v$) equals $e$; let $w$ be an endomorphism of $A \times_{\operatorname{Spec} B} A$ with $w$ followed by the first projection equal to the first projection followed by $u$, and $w$ followed by the second projection equal to the second projection followed by $v$ (so $w = u \times v$). Then, with $\Lambda(\mathcal L) = \mathrm{add}^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ the Mumford bundle on $A \times_{\operatorname{Spec} B} A$ and $\mathrm{sliceAt}\,f\,e = \langle p_1, p_2 \circ e\rangle : A \times_{\operatorname{Spec} B} \operatorname{Spec} B \to A \times_{\operatorname{Spec} B} A$ the unit slice, both pullbacks of $w^*\Lambda(\mathcal L)$ — along the unit slice, and along the unit slice composed with the symmetry of the fibre product — admit an isomorphism to the unit module, each asserted as a `Nonempty` statement.
--
--   This is the birigidification input for the Mumford bundle of an invertible module twisted by a pair of endomorphisms fixing the unit section: over a local base, $(u\times v)^*\Lambda(\mathcal L)$ is trivial along both unit slices. With $u = v = \mathrm{id}$ it is the statement that $\Lambda(\mathcal L)$ is birigidified over a local base; in the form stated it is used in the treatment of Rosati-compatibility for fake elliptic curves with quaternionic multiplication, where $u$ or $v$ is an action endomorphism and the other the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
    {B : Type} [CommRing B] [IsLocalRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hA : AbelianSchemePropertyBundle B f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (u v : A ⟶ A) (hu : u ≫ f = f) (hv : v ≫ f = f)
    (hue : (L.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ u = (L.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (hve : (L.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ v = (L.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (w : pullback f f ⟶ pullback f f)
    (hw₁ : w ≫ pullback.fst f f = pullback.fst f f ≫ u) (hw₂ : w ≫ pullback.snd f f = pullback.snd f f ≫ v) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))))).obj
        ((Scheme.Modules.pullback w).obj (mumfordBundle f L 𝓛)) ≅ 𝟙_ _) ∧
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj
          ((Scheme.Modules.pullback w).obj (mumfordBundle f L 𝓛))) ≅ 𝟙_ _) := by sorry

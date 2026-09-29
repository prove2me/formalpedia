-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_forall_iff_isInStabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/bf0a5d33-335b-5f28-908b-87e3a9007d9d
-- title:
--   Stabiliser K(L) is a closed subscheme of A
-- statement:
--   Let $R$ be a Noetherian commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a proper, flat morphism with geometrically integral fibres. Let $L$ be a relative group law on $f$: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} R$ it equips the set of $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$ with a multiplication, a unit and an inversion satisfying associativity, the two unit laws and left inverses, the multiplication being natural under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$. Assume further that for every commutative $R$-algebra $B$ the map on global sections induced by the projection $A \times_{\operatorname{Spec} R} \operatorname{Spec} B \to \operatorname{Spec} B$ is bijective. Let $\mathcal L$ be a module on $A$ that is invertible, i.e. every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module of $U$. Then there are a scheme $K$ and a closed immersion $\iota : K \to A$ such that for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and every $x : T \to A$ over $t$, the morphism $x$ factors as some $k : T \to K$ followed by $\iota$ if and only if $x$ lies in the stabiliser of $\mathcal L$, that is, the pullback of $\mathcal L$ along the relative translation $L.\mathrm{mulRight}\,t\,x : A \times_{\operatorname{Spec} R} T \to A$ and the pullback of $\mathcal L$ along the first projection are locally isomorphic over $T$: every point of $T$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic.
--
--   This is Mumford's stabiliser subscheme $K(\mathcal L)$ of an invertible sheaf on a group scheme, here over an arbitrary Noetherian base and with no finiteness assertion about $\iota$ (finiteness requires further input, such as ampleness). It is used to transport the triviality of $K(\mathcal L)$ between fibres, complete local rings and neighbourhoods in the base in the construction of canonical polarisations of abelian schemes, and is cited in the treatment of Mumford bundles, Riemann forms and the refinement in which the stabiliser immersion is moreover finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_forall_iff_isInStabilizer
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [IsProper f] [Flat f] [GeometricallyIntegral f] (L : RelativeGroupLaw R f)
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (KL : Scheme.{u}) (ι : KL ⟶ A), IsClosedImmersion ι ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (∃ k : T ⟶ KL, k ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x := by sorry

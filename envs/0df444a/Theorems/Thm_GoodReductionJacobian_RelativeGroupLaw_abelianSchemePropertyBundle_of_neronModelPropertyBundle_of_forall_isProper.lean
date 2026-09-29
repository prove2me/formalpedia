-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper
-- name    : GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/78c5287d-bb7f-5a9b-9a0a-86ed1be825d4
-- title:
--   Néron model with proper identity component is an abelian scheme
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with `IsDiscreteValuationRing`), $K$ a field that is an $R$-algebra and a fraction field of $R$, $B$ a scheme and $g : B \to \operatorname{Spec} R$ a morphism. Assume given `LB`, a relative group law for $g$ over $R$: for every $R$-scheme $t : T \to \operatorname{Spec} R$ a multiplication, unit and inverse on the set $\{\varphi : T \to B \mid \varphi \text{ followed by } g = t\}$, satisfying associativity, both unit laws and left inverse, with multiplication natural under morphisms $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume `hN`, that $g$ is smooth, separated, locally of finite type and quasi-compact and satisfies the Néron mapping property, i.e. for every smooth $t : T \to \operatorname{Spec} R$ restriction to the generic fibre, `genericFibreRestrict`, is bijective on sections. Assume `hBK`, that the generic fibre $\operatorname{pr}_2 : B \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ is smooth and proper, has connected set-theoretic fibres over every point of $\operatorname{Spec} K$, and carries a relative group law over $K$. Assume finally `hproper`: for every scheme $G_0$ and every open immersion $i : G_0 \to B \times_{\operatorname{Spec} R} \operatorname{Spec} k$, where $k$ is the residue field of $R$ and the fibre product is taken along $\operatorname{Spec}$ of the residue map, whose range is the connected component of the point obtained by evaluating the unit section of the base-changed group law at the identity of $\operatorname{Spec} k$ at the closed point of $\operatorname{Spec} k$, the composite of $i$ with the projection to $\operatorname{Spec} k$ is proper. Then $g$ is smooth and proper, all its set-theoretic fibres over points of $\operatorname{Spec} R$ are connected, and $g$ carries a relative group law over $R$.
--
--   This is the implication (a) $\Rightarrow$ (b) of the classical criterion identifying a Néron model whose special-fibre identity component is proper with an abelian scheme (Bosch–Lütkebohmert–Raynaud 7.4, Theorem 5; Serre–Tate §1), here in the shape: properness of every open subscheme of the special fibre cutting out the identity component forces properness of the whole Néron model. It feeds the good-reduction criterion for the Jacobians occurring in the modularity argument, being cited by the companion statement [`GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self`](thm.html#GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (hproper : ∀ (G₀ : Scheme.{u})
        (i : G₀ ⟶ pullback g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
        [IsOpenImmersion i],
        Set.range i =
          connectedComponent
            (((LB.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).one
                (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))).1
              (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) →
        IsProper (i ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) :
    AbelianSchemePropertyBundle R g := by sorry

-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/637d0da4-9215-580b-b55a-64312aa86ab0
-- title:
--   Rigidity: a homomorphism fixing one geometric fibre is the identity
-- statement:
--   Let $R$ be a noetherian integral domain, let $A$ be a scheme and let $f : A \to \operatorname{Spec} R$ satisfy `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law for $f$ exists. Let $L$ be such a relative group law: for every $t : T \to \operatorname{Spec} R$ it equips the set of $R$-morphisms $T \to A$ over $t$ with a group structure, naturally in $T$. Let $\sigma$ be a morphism $A \to A$ with $\sigma$ followed by $f$ equal to $f$, and assume $\sigma$ is a homomorphism on points: for every $t : T \to \operatorname{Spec} R$ and all $x, y$ over $t$, composing $L$-product $L.\mathrm{mul}\,t\,x\,y$ with $\sigma$ equals the $L$-product of $x$ followed by $\sigma$ and $y$ followed by $\sigma$. Let $\mathfrak p \subset R$ be a maximal ideal and assume that $\sigma$ acts as the identity on the geometric fibre over $\mathfrak p$: for every algebraically closed field $K$, every ring homomorphism $\kappa : R/\mathfrak p \to K$ and every point $x$ over $\operatorname{Spec}$ of $R \to R/\mathfrak p \xrightarrow{\kappa} K$, one has $x$ followed by $\sigma$ equal to $x$. Then $\sigma$ is the identity of $A$, as an element of the morphisms over $f$.
--
--   This is the rigidity statement for homomorphisms of abelian schemes over a connected base, here $\operatorname{Spec}$ of a noetherian domain: the locus of points whose geometric fibre is pointwise fixed is open and closed, hence everything. It is used in the construction of polarised abelian schemes, where an endomorphism is identified with the identity after checking it on a single geometric fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eq_schemeHomOverId_of_forall_schemeHomOverComp_eq_quotient_of_isDomain
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (L : RelativeGroupLaw R f) (σ : SchemeHomOver f f)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (𝔭 : Ideal R) [𝔭.IsMaximal]
    (hfix : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : R ⧸ 𝔭 →+* K)
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (κ.comp (Ideal.Quotient.mk 𝔭)))) f),
      NeronModelInfra.schemeHomOverComp x σ = x) :
    σ = NeronModelInfra.schemeHomOverId f := by sorry

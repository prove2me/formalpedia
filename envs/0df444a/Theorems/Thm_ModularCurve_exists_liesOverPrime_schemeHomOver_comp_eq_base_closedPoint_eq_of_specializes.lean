-- Prove2me | Theorems.Thm_ModularCurve_exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes
-- name    : ModularCurve.exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8f7a43ae-3727-570c-a9da-1fd87bd1a6e1
-- title:
--   Valuation-ring lift of a ℚ̄-point along a specialisation
-- statement:
--   Fix a prime $p$ and write $R = \mathrm{ratLocalizedAt}\,p$ for the subring of $\mathbf Q$ consisting of those rationals whose denominator is coprime to $p$. Let $X$ be a scheme and $c : X \to \operatorname{Spec} R$ a proper morphism. Suppose given, for every valuation subring $A$ of a fixed algebraic closure $\bar{\mathbf Q}$ of $\mathbf Q$ satisfying $\mathrm{LiesOverPrime}$, i.e. such that the image of $p$ in $\bar{\mathbf Q}$ lies in the nonunits of $A$, a ring homomorphism $\rho_A : R \to A$, and assume each $\rho_A$ composed with the inclusion $A \hookrightarrow \bar{\mathbf Q}$ is the structure map $R \to \bar{\mathbf Q}$. Let $x_\eta : \operatorname{Spec}\bar{\mathbf Q} \to X$ be a morphism with $x_\eta$ followed by $c$ equal to $\operatorname{Spec}$ of $R \to \bar{\mathbf Q}$, and let $x$ be a point of $X$ to which the image under $x_\eta$ of the closed point of $\operatorname{Spec}\bar{\mathbf Q}$ specialises. Assume finally that the germ at $x$ of the global section of $X$ obtained by pulling back the element $p$ of $R$ along $c$ is not a unit in the stalk $\mathcal O_{X,x}$. Then there exist a valuation subring $A \subseteq \bar{\mathbf Q}$ with $p$ a nonunit of $A$ and a morphism $x_A : \operatorname{Spec} A \to X$ whose composite with $c$ is $\operatorname{Spec}$ of $\rho_A$ (this is what membership in `SchemeHomOver` records), such that precomposing $x_A$ with $\operatorname{Spec}$ of the inclusion $A \hookrightarrow \bar{\mathbf Q}$ gives $x_\eta$, and $x_A$ sends the closed point of $\operatorname{Spec} A$ to $x$.
--
--   This is the horizontal lifting step in the style of the valuative criterion of properness: a $\bar{\mathbf Q}$-point of a scheme over $\mathbf Z_{(p)}$ is extended to a point with values in a valuation ring of $\bar{\mathbf Q}$ above $p$, with prescribed reduction. It feeds the analysis of stalks and germs of a rational curve model of a modular curve at a point of the fibre above $p$, where $\mathbf Z_{(p)}$ appears as the subring of rationals with denominator coprime to $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

theorem ModularCurve.exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes
    (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsProper c]
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (xη : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X)
    (hxη : xη ≫ c = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))
    (x : X) (hPx : xη.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ x)
    (hx : ¬ IsUnit ((X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))))) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 = xη ∧
      xA.1.base (IsLocalRing.closedPoint ↥A) = x := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/df27585b-70f9-5538-8410-e3e8419445f2
-- title:
--   Valuative extension of a geometric point to an A-section
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number with $p \mid M$, let $H \le (\mathbb{Z}/M)^{\times}$, and let $hj$ record that the $q$-expansion `jqModC ℚ` of $j$ lies in the function field `qExpFunctionFieldC ℚ ⊤` attached to the full modular group. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`; its data include properness and flatness of the structure morphism `toBase p (ΓM M H) hj` of the two-chart integral model `X p (ΓM M H) hj` over $\mathrm{Spec}\,(\mathrm{R}\,p)$, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ for the function field `xHFunctionFieldBar M H` together with an isomorphism $\mathfrak{X}.\mathrm{eeta}$ from $\mathfrak{X}.\mathrm{Meta}.C$ onto the base change of `toBase p (ΓM M H) hj` along $\mathrm{R}\,p \to \overline{\mathbb{Q}}$ satisfying $\mathfrak{X}.\mathrm{eeta}$ followed by `pullback.snd` $= \mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (the predicate `A.LiesOverPrime p`), whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map of $\mathrm{R}\,p$. Finally let $y$ be a section of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, i.e. a morphism $\mathrm{Spec}\,\overline{\mathbb{Q}} \to \mathfrak{X}.\mathrm{Meta}.C$ composing with $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ to the identity. The assertion is the existence of: a morphism $u : \mathrm{Spec}\,A \to$ `X p (ΓM M H) hj` over $\mathrm{Spec}\,\rho$, whose restriction along $\mathrm{Spec}\,(A \hookrightarrow \overline{\mathbb{Q}})$ equals the geometric point $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and `pullback.fst`; a morphism $u_\kappa$ from $\mathrm{Spec}\,\kappa$ to the fibre `fibre ((IsLocalRing.residue ↥A).comp ρ)`, namely the base change of `toBase p (ΓM M H) hj` along $\mathrm{R}\,p \to \kappa$, whose first projection is $\mathrm{Spec}$ of the residue map followed by $u$ and whose second projection is the identity; and an index $i \in \{0,1\}$ together with a closed point $P_0$ of $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ such that the image of $P_0$ under $\mathfrak{X}.\mathrm{efib}\,A\,hA\,\rho\,h\rho$ followed by $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,i$ is the point $u_\kappa(\text{closed point of }\kappa)$.
--
--   This is the valuative criterion of properness applied to the integral model of $X_H(M)$ at a prime $p$ dividing $M$: a geometric point of the generic fibre spreads out to a section over a valuation ring $A$ of $\overline{\mathbb{Q}}$ above $p$, and the resulting closed point of the special fibre is recognised on one of the two components through the fibre curve model. It is used downstream in the analysis of specialisations of points and cusps on such models, for instance in the statements on cusp orientations and on Néron-model points at level $p$ that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) :
    ∃ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (i : Fin 2) (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by sorry

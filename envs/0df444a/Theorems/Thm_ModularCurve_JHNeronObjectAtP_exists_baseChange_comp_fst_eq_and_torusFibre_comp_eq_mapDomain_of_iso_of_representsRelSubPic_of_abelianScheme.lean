-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_baseChange_comp_fst_eq_and_torusFibre_comp_eq_mapDomain_of_iso_of_representsRelSubPic_of_abelianScheme
-- name    : ModularCurve.JHNeronObjectAtP.exists_baseChange_comp_fst_eq_and_torusFibre_comp_eq_mapDomain_of_iso_of_representsRelSubPic_of_abelianScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/04ee80d5-e1ec-504e-a85c-80d1f3c85af5
-- title:
--   Transport of the torus along an isomorphism of Néron objects
-- statement:
--   Fix a prime $p$, a positive integer $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis $hj$ that the Laurent series `jqModC` over $\mathbb{Q}$ lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ and with residue field algebraically closed of characteristic $p$. Let $\Lambda, \Lambda'$ be level data over $A$ for $J_H$ at $p$, and $O, O'$ Néron objects at $p$ over $\Lambda$, $\Lambda'$ respectively, each given with a hypothesis $hD$, $hD'$ that its structure morphism $g$ together with the unit section of its group law represents, in the sense of `RepresentsRelSubPic`, the relative Picard functor of $\mathfrak{X}$'s curve $\mathrm{toBase}$ over $R_p$ rigidified along $\mathfrak{X}.\varepsilon_{\mathrm{inf}}$ and cut out by the condition that the rigidified line bundle be fibrewise algebraically equivalent to zero. Assume $\Lambda'.f$ satisfies `AbelianSchemePropertyBundle` over `baseRing p` (smooth, proper, connected fibres, and admitting a relative group law). Let $\psi$ and $\psi^{-1}$ be mutually inverse morphisms between $O.G$ and $O'.G$ over `base p`, with $\psi$ a homomorphism for the two group laws induced by $hD$ and $hD'$ on all $T$-points. Then there is a morphism $\psi_\kappa$ between the base changes of $O.g$ and $O'.g$ along $\mathrm{resPt}(A)$ followed by $\Lambda.\sigma_A$, respectively $\Lambda'.\sigma_A$, compatible with $\psi$ via the first projections, and an isomorphism of additive groups $M_x : \mathbb{Z}^{O'.\mathrm{toricRank}} \to \mathbb{Z}^{O.\mathrm{toricRank}}$ such that the torus fibre of $O$ followed by $\psi_\kappa$ equals $\operatorname{Spec}$ of the group-algebra map induced by $M_x$ over the residue field of $A$ followed by the torus fibre of $O'$.
--
--   This is the transport statement for the toric part of the special fibre of the Néron object: any isomorphism of two representatives of the relative Picard group law, one of which has abelian-scheme special fibre, descends to the geometric special fibre over the residue field and matches the split tori up to an automorphism of their character lattices. It is used in the analysis of the inertia action on points of $J_H$ at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_baseChange_comp_fst_eq_and_torusFibre_comp_eq_mapDomain_of_iso_of_representsRelSubPic_of_abelianScheme.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_baseChange_comp_fst_eq_and_torusFibre_comp_eq_mapDomain_of_iso_of_representsRelSubPic_of_abelianScheme
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f)
    (ψ : SchemeHomOver O.g O'.g) (ψinv : SchemeHomOver O'.g O.g)
    (hψ₁ : ψ.1 ≫ ψinv.1 = 𝟙 _) (hψ₂ : ψinv.1 ≫ ψ.1 = 𝟙 _)

    (hψmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) ψ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul s
          (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)) :
    ∃ ψκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ'.σA) O'.g),
      ψκ.1 ≫ pullback.fst O'.g (resPt A ≫ Λ'.σA) = pullback.fst O.g (resPt A ≫ Λ.σA) ≫ ψ.1 ∧
      ∃ Mx : (Fin O'.toricRank → ℤ) ≃+ (Fin O.toricRank → ℤ),
        O.torusFibre.1 ≫ ψκ.1 =
          Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A)
            (Mx : (Fin O'.toricRank → ℤ) →+ (Fin O.toricRank → ℤ)))) ≫ O'.torusFibre.1 := by sorry

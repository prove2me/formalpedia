-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
-- name    : ModularCurve.JHNeronObjectAtP.exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/cad9aa0a-c015-5c6e-b0d3-e3f472644a81
-- title:
--   Transport of toric lifts along an isomorphism of Néron objects
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^{2} \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a witness `hj` that `jqModC ℚ` lies in the $q$-expansion function field of full level, so that the two-chart integral model morphism `toBase p (ΓM M H) hj` over `R p` is defined; let `𝔛 : XHDRModelAtP p M H hpM hj` be Deligne–Rapoport model data for it, with section `𝔛.εinf`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ for which $p$ is a nonunit, with algebraically closed residue field of characteristic $p$. Let `Λ`, `Λ'` be level data at $p$ over $A$ and `O`, `O'` Néron objects `JHNeronObjectAtP` over them. Assume `hD`, `hD'`: the designations formed from `O.G`, `O.g` (respectively `O'.G`, `O'.g`) together with the identity element of the relative group law at the base identity as zero section represent the functor of rigidified line bundles on `toBase p (ΓM M H) hj` rigidified along `𝔛.εinf` and algebraically equivalent to zero on all geometric fibres; assume `hpts_law`, `hpts_law'`: the parametrisations `O.pts`, `O'.pts` of $J_H(M)$ by generic points are additive for the relative group laws supplied by `hD`, `hD'`; assume `hΛ'`: the structure morphism `Λ'.f` is smooth and proper with connected fibres and carries a relative group law. Let $\psi$, $\psi^{-1}$ be morphisms over `base p` between `O.g` and `O'.g` that are mutually inverse, with $\psi$ compatible with the two relative group laws on all test bases. Then for every $m > 0$ there is a bijection $a$ from the set of $A$-algebra homomorphisms $A[(\mathbb{Z}/m)^{O.\mathtt{toricRank}}] \to \overline{\mathbb{Q}}$ to the set of $A$-algebra homomorphisms $A[(\mathbb{Z}/m)^{O'.\mathtt{toricRank}}] \to \overline{\mathbb{Q}}$ such that for every such character $\chi$ the morphism underlying `O'.pts (O'.toricPoint m hm (a χ))` equals the morphism underlying `O.pts (O.toricPoint m hm χ)` followed by $\psi$.
--
--   This is the rigidity statement that the toric part of a Néron object at a prime exactly dividing the level is transported by any isomorphism of such objects, up to a relabelling of the $\mu_m$-characters: the two toric lifts of $\mu_m^{t}$ differ only by an automorphism of the character group. It feeds the comparison of toric and finite points that produces a Galois-equivariant identification of the two Néron objects' point groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f)
    (hpts_law' : ∀ x y : JH M H,
        O'.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul _ (O'.pts x) (O'.pts y))
    (ψ : SchemeHomOver O.g O'.g) (ψinv : SchemeHomOver O'.g O.g)
    (hψ₁ : ψ.1 ≫ ψinv.1 = 𝟙 _) (hψ₂ : ψinv.1 ≫ ψ.1 = 𝟙 _)

    (hψmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) ψ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul s
          (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)) :
    ∀ (m : ℕ) (hm : 0 < m),
      ∃ a : (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) ≃ (muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
        ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          (O'.pts (O'.toricPoint m hm (a χ))).1 = (O.pts (O.toricPoint m hm χ)).1 ≫ ψ.1 := by sorry

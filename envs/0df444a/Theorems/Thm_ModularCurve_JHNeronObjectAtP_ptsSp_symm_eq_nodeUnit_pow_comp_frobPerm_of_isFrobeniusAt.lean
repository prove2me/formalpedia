-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_nodeUnit_pow_comp_frobPerm_of_isFrobeniusAt
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_nodeUnit_pow_comp_frobPerm_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/71e25b85-b5ca-5f95-8bc5-1d5d8d97eef3
-- title:
--   Frobenius on node units: p-th power twisted by the crossing permutation
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$. Assume $j$ lies in the level-one $q$-expansion function field over $\mathbb{Q}$, and let $\mathfrak{X}$ be an `XHDRModelAtP` for these data. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H` which, on elements whose Laurent expansion comes from level $M/p$ with character group `infSubgroup p M H hpM`, acts by $q \mapsto q^{p}$ (the hypothesis `hθ`), and assume `hwgen`: precomposition of an $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.\mathrm{Meta}.C$ with $\mathfrak{X}.w$ translates the associated place of the function field by the semilinear automorphism attached to $\theta$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit, whose residue field is algebraically closed of characteristic $p$, and $\rho : R_p \to A$ a lift of the structure map to $\overline{\mathbb{Q}}$. Let $\Lambda$ be level data and $O$ a Néron object for $J_H(M)$ at $A$, with $O.G$ representing the relative $\mathrm{Pic}^0$ of $\mathfrak{X}$ cut out by fibrewise algebraic triviality (`hD`), with $\Lambda.\sigma_A = \operatorname{Spec}\rho$, and with the point-reduction dictionary `hsp` relating degree-zero divisor classes on the generic geometric fibre to glued data on the special fibre (grouped here as one hypothesis). Let $\mathrm{perm}$ be a permutation of the crossing set $O.\mathrm{ssFinset}$ acting on both coordinates of each crossing by `qExpFrobeniusPlaceModL` at $p$, and let $\varphi$ be an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lying in the decomposition subgroup of $A$ and inducing $x \mapsto x^{p}$ on the residue field. Finally let $x \in J_H(M)$, let $s, s'$ be $A$-points of $O.G$ extending the $\overline{\mathbb{Q}}$-points $O.\mathrm{pts}\,x$ and $O.\mathrm{pts}(\varphi \cdot x)$, and suppose the reduction of $s$, read through $O.\mathrm{ptsSp}^{-1}$, is the node-unit class of $w : O.\mathrm{ssFinset} \to \mathrm{Additive}\,\kappa^\times$ (the class of the glued datum $(0,0,w)$). Then the reduction of $s'$ is the node-unit class of $t \mapsto p \cdot w(\mathrm{perm}^{-1} t)$, that is, of $t \mapsto w(\mathrm{perm}^{-1}t)^{p}$ multiplicatively.
--
--   This is the Galois action on the toric part of the special fibre of the Néron model of $J_H(M)$ at a prime exactly dividing the level: a Frobenius element acts on node units by raising values to the $p$-th power and transporting them along the Frobenius permutation of the supersingular crossings. It feeds the computations of the action of the diamond and $U_p$ operators on Tate modules and the resulting lattice statements used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_nodeUnit_pow_comp_frobPerm_of_isFrobeniusAt.lean

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

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_nodeUnit_pow_comp_frobPerm_of_isFrobeniusAt
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (perm : Equiv.Perm ↥O.ssFinset)
    (hperm : ∀ t : ↥O.ssFinset,
      ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
          (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
      ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
          (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
    (x : JH M H) (s s' : SchemeHomOver Λ.σA O.g)
    (hs : (O.pts x).1 = barPt A ≫ s.1) (hs' : (O.pts (φ • x)).1 = barPt A ≫ s'.1)
    (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (hw : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset w) :

    O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s') =
      GluedPic0.nodeUnit O.ssFinset (fun t => p • w (perm.symm t)) := by sorry

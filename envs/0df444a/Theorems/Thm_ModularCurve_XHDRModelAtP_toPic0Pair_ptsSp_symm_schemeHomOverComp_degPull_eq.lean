-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq
-- name    : ModularCurve.XHDRModelAtP.toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/ae53cdf6-cc48-5f5b-a712-2e0ab6b8e550
-- title:
--   Special fibre of the degeneracy pull-backs on Pic⁰ coordinates
-- statement:
--   Fix a prime $p$ and an integer $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and divisibility data $p \mid M$ together with $\neg\, p^{2} \mid M$ (so $p$ exactly divides $M$), with $M/p$ nonzero; the hypothesis `hHp` requires that every unit $u$ of $\mathbb{Z}/M$ whose image under reduction to $(\mathbb{Z}/(M/p))^{\times}$ is trivial belongs to $H$. Let `hj` assert that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-one $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` over $\mathbb{Q}$, so that the two-chart integral models `X p Γ hj` and their structure morphisms `toBase p Γ hj` to $\operatorname{Spec}$ of the base ring `R p` are available for the level groups `ΓM M H` and `ΓN p M H hpM`. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, the Deligne–Rapoport type integral model datum at $p$ for the level-$H(M)$ curve, carrying in particular the section `𝔛.εinf`, the degeneracy morphisms `𝔛.π` and `𝔛.πw`, the smooth locus `𝔛.smoothLocus`, and, for a place as below, the curve model `𝔛.Mfib A hA ρ hρ` of the special fibre with its morphisms `𝔛.efib A hA ρ hρ` and `𝔛.comp A hA ρ hρ i` ($i \in \{0,1\}$) onto the two components. The morphism `toBase p (ΓM M H) hj` is assumed proper and separated, and `toBase p (ΓN p M H hpM) hj` separated.
--
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, that is $p$ lies in the non-units of $A$, whose residue field $\kappa = \mathrm{ResidueField}\ A$ has characteristic $p$ and is algebraically closed, and let $\rho : R p \to A$ be a ring homomorphism with $A.\mathrm{subtype} \circ \rho$ equal to the structure map $R p \to \overline{\mathbb{Q}}$. Write $\bar F =$ `Fbar p M H hpM κ` for the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)`.
--
--   Representing data. $D$ is a relative $\mathrm{Pic}^0$ designation over `R p` for `toBase p (ΓM M H) hj` (a scheme with a structure morphism to $\operatorname{Spec}(R p)$ and a zero section), and `hD` asserts that $D$ represents, with Poincaré bundle `hD.poincare`, the subfunctor of line bundles on the level-$\Gamma M$ model rigidified along `𝔛.εinf` cut out by `algEquivZeroCut`, i.e. by the condition `FibrewiseAlgEquivZero`: for every algebraically closed field $k$ and every $k$-point of the base, the pullback of the bundle to the corresponding fibre is algebraically equivalent to zero. Likewise $D_0$ is such a designation for `toBase p (ΓN p M H hpM) hj`, and `hD₀` asserts that $D_0$ represents the corresponding subfunctor for bundles rigidified along `𝔛.εinf` composed with `𝔛.π`.
--
--   Special-fibre dictionaries. `ptsSp₀` is a bijection from $\mathrm{Pic}^0(\kappa,\bar F)$, the group of degree-zero divisor classes modulo principal divisors, onto the set of points of $D_0$ over `resPt A ≫ Spec.map ρ` (the $\kappa$-point of the base obtained from $\rho$ and the residue map of $A$). Hypothesis `hptsSp₀_add` states that `ptsSp₀` is additive for the group law on these points obtained from the relative group law attached to `hD₀` by base change along that $\kappa$-point. Hypothesis `hptsSp₀` is the pinning of `ptsSp₀` on differences of sections: given two $A$-points $v_1,v_2$ of the level-$\Gamma N$ model over $\operatorname{Spec}\rho$, $\kappa$-points $v\kappa_1,v\kappa_2$ of the fibre of that model at the composite residue homomorphism satisfying the two compatibility identities (first projection equal to $v_j$ reduced, second projection the identity), closed points $Q_1,Q_2$ of the curve model `(𝔛.Mfib A hA ρ hρ).C` whose images under `𝔛.efib` are the closed points determined by $v\kappa_1,v\kappa_2$, and a degree-zero divisor $D_w$ equal to the difference of the single divisors at the places of $Q_1$ and of $Q_2$, there exists a point $s_0$ of $D_0$ over $\operatorname{Spec}\rho$ such that the pullback of the Poincaré bundle of $D_0$ along $s_0$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the section $v_1$ with the ideal module of that of $v_2$ (that is, $\mathcal{O}(v_1-v_2)$), and such that `ptsSp₀.symm` of the restriction of $s_0$ to the $\kappa$-point equals the class of $D_w$.
--
--   `SS` is a finite set of pairs of places of $\bar F$ over $\kappa$, and `hSS` states that its members are exactly the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, namely the pairs whose second entry is a supersingular place and whose first entry is its image under the mod-$p$ Frobenius place map. `ptsSp` is a bijection from `GluedPic0 κ F̄ SS` — the quotient of the admissible gluing data (pairs of degree-zero divisors, each vanishing at the relevant entry of every pair in `SS`, together with a family of units indexed by `SS`) by the glued principal data — onto the points of $D$ over `resPt A ≫ Spec.map ρ`; `hptsSp_add` states its additivity for the group law coming from the relative group law attached to `hD`, base changed along that $\kappa$-point. Hypothesis `hptsSp` pins `ptsSp` on same-component differences inside the smooth locus: for $i \in \{0,1\}$, given $A$-points $u_1,u_2$ of the level-$\Gamma M$ model over $\operatorname{Spec}\rho$ whose set-theoretic ranges lie in `𝔛.smoothLocus`, $\kappa$-points $u\kappa_1,u\kappa_2$ of the fibre satisfying the same two compatibility identities, closed points $P_1,P_2$ of `(𝔛.Mfib A hA ρ hρ).C` whose images under `𝔛.efib` followed by `𝔛.comp … i` are the closed points determined by $u\kappa_1,u\kappa_2$, and an admissible gluing datum $x$ whose first divisor component is the difference of the single divisors at the places of $P_1$ and $P_2$ if $i=0$ and zero otherwise, whose second divisor component is that same difference if $i=1$ and zero otherwise, and whose unit component is zero, there exists a point $s$ of $D$ over $\operatorname{Spec}\rho$ with the pullback of the Poincaré bundle of $D$ along $s$ isomorphic to the line bundle of the relative effective Cartier divisor of $u_1$ tensored with the ideal module of that of $u_2$, and with `ptsSp.symm` of the restriction of $s$ to the $\kappa$-point equal to the class of $x$.
--
--   Degeneracy classifying morphisms. `degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase` is a pair of morphisms $D_0 \to D$ over $\operatorname{Spec}(R p)$, and `hdegPull` states that for each $i$, every scheme $T$ with a morphism $t$ to $\operatorname{Spec}(R p)$ and every $T$-point $b$ of $D_0$, the pullback of the Poincaré bundle of $D$ along $b$ followed by `degPull i` is isomorphic to the rigidification, along the section `rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf` and the projection, of the pullback along the curve change of `𝔛.π` (for $i=0$) or of `𝔛.πw` (for $i=1$) of the pullback of the Poincaré bundle of $D_0$ along $b$; thus `degPull 0` and `degPull 1` classify pull-back of rigidified bundles along $\pi$ and along $\pi w$ respectively.
--
--   Frobenius and diamond data. $F$, $F^{-1}$ (written `Finv`) and $F^{*}$ (written `Fstar`) are additive endomorphisms of $\mathrm{Pic}^0(\kappa,\bar F)$, `pb` is a unit of $\mathbb{Z}/(M/p)$, and $\delta$ is a further additive endomorphism, subject to: `hF`, that $F$ is the mod-$p$ Frobenius push-forward `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`; `hFinv`, that $F \circ F^{-1}$ and $F^{-1} \circ F$ are both the identity; `hFstar`, that $F^{*}z = p \cdot F^{-1}z$ for all $z$; `hpb`, that the image of `pb` in $\mathbb{Z}/(M/p)$ is the class of $p$; and `hδ`, that $\delta z$ is the action on $z$ of the semilinear automorphism attached, via `SemilinearAut.ofAlgAut`, to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of `pb`, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$.
--
--   Conclusion: for every $i \in \{0,1\}$ and every point $x$ of $D_0$ over `resPt A ≫ Spec.map ρ`, writing $z =$ `ptsSp₀.symm x` for the corresponding degree-zero divisor class, the image under `GluedPic0.toPic0Pair SS` of `ptsSp.symm` of the composite of $x$ with `degPull i` — that is, the pair of classes of the two divisor components of the glued datum — equals $(z, F^{*}z)$ if $i = 0$, and $(F^{*}z, \delta z)$ if $i = 1$.
--
--   This records, in the glued coordinates on the special fibre at a prime $p$ exactly dividing the level $M$, the classical description of the two degeneracy pull-backs on $\mathrm{Pic}^0$ of the Deligne–Rapoport fibre: $\pi^{*}z = (z, F^{*}z)$ and $(\pi w)^{*}z = (F^{*}z, \langle p\rangle z)$, where $F^{*} = p\,F^{-1}$ is the transpose of the Frobenius push-forward and $\langle p \rangle$ the diamond operator at level $M/p$. It is used by [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords) in the construction of the level-$H(M)$ Néron object at $p$, which feeds the local analysis at $p$ in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq.lean

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
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.toPic0Pair_ptsSp_symm_schemeHomOverComp_degPull_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase)

    (hptsSp₀_add : ∀ a b, ptsSp₀ (a + b) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
        (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b))))

    (hptsSp₀ : ∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hptsSp_add : ∀ x y, ptsSp (x + y) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
        (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y))))
    (hptsSp : ∀ (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hD.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x)

    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L)))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z) :
    ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase),
      GluedPic0.toPic0Pair SS (ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (ptsSp₀.symm x, Fstar (ptsSp₀.symm x))
        else (Fstar (ptsSp₀.symm x), δ (ptsSp₀.symm x)) := by sorry

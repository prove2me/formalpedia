-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ptsSp_gluedPic0_dictionary_specialFibre
-- name    : ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/eb49a294-f7bf-5398-96c3-8e6b1c4a7800
-- title:
--   Glued special-fibre dictionary for relative Pic⁰ at p ‖ M
-- statement:
--   Setting. Fix a prime $p$ and $M\ge 1$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` of $SL_2(\mathbb{Z})$. For a congruence subgroup $\Gamma$ the morphism `toBase p Γ hj : X p Γ hj ⟶ Spec (R p)` is the structure morphism of the two-chart integral model over the base ring `R p` built from `qExpFunctionFieldC ℚ Γ` and the coordinate `jAt Γ hj`; it is used at the two levels $\Gamma_M =$ `ΓM M H` and $\Gamma_N =$ `ΓN p M H hpM`, and both structure morphisms are assumed separated. The datum $\mathfrak{X}$ is a term of the structure `XHDRModelAtP p M H hpM hj`; of its fields the following are used: the section `𝔛.εinf` of `toBase p (ΓM M H) hj` over the identity of $\mathrm{Spec}\,R_p$, the morphism `𝔛.π` from the level-$\Gamma_M$ model to the level-$\Gamma_N$ model over $\mathrm{Spec}\,R_p$ (so that `schemeHomOverComp 𝔛.εinf 𝔛.π` is a section of the level-$\Gamma_N$ model), the set `𝔛.smoothLocus` of points of `X p (ΓM M H) hj`, and, for the place data below, a curve model `𝔛.Mfib A hA ρ hρ` over the residue field with function field `Fbar p M H hpM (ResidueField ↥A)`, a morphism `𝔛.efib A hA ρ hρ` from its underlying scheme to the level-$\Gamma_N$ special fibre, and two morphisms `𝔛.comp A hA ρ hρ i` ($i \in \mathrm{Fin}\,2$) from the level-$\Gamma_N$ special fibre to the level-$\Gamma_M$ special fibre.
--
--   Place data. $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, i.e. $p$ lies in the non-units of $A$; its residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed; and $\rho : R_p \to A$ is a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structural map $R_p \to \overline{\mathbb{Q}}$. Throughout, $\iota$ denotes the composite `resPt A ≫ Spec.map (CommRingCat.ofHom ρ)`, namely $\mathrm{Spec}\,\kappa \to \mathrm{Spec}\,A \to \mathrm{Spec}\,R_p$, and $\bar F =$ `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)`. Places of $\bar F$ over $\kappa$ are valuation subrings of $\bar F$ containing $\kappa$, different from $\bar F$ and principal; $\mathrm{Div}$, $\mathrm{Div}^0$ and $\mathrm{Pic}^0$ are the free abelian group on places, its degree-zero subgroup and its quotient by the principal divisors.
--
--   $\mathrm{Pic}^0$ designations. $D$ is a `RelativePic0Designation` for `toBase p (ΓM M H) hj` over $R_p$ (a scheme with a structure morphism `D.toBase` to $\mathrm{Spec}\,R_p$ and a zero section), and `hD` asserts that $D$ represents the rigidified relative Picard functor of the pair (`toBase p (ΓM M H) hj`, `𝔛.εinf`) cut out by `algEquivZeroCut`, the condition that a rigidified line bundle be fibrewise algebraically equivalent to zero: it supplies a Poincaré rigidified bundle `hD.poincare` satisfying the condition, the universal property that every such bundle on a base $T$ is induced along a unique $T$-point of `D.toBase`, and triviality along the zero section. Likewise $D_0$ and `hD₀` do the same for `toBase p (ΓN p M H hpM) hj` with the section `schemeHomOverComp 𝔛.εinf 𝔛.π`.
--
--   Level-$\Gamma_N$ dictionary. `ptsSp₀` is a bijection $\mathrm{Pic}^0(\kappa, \bar F) \simeq$ (the set of points of `D₀.toBase` over $\iota$). The hypothesis `hptsSp₀_add` states that `ptsSp₀` is additive for the group law on these points obtained by base-changing along $\iota$ the relative group law attached to `hD₀` (via `algEquivZeroGroupCut`), transport between points over $\iota$ and points of the base change over the identity being by `toFibrePt`/`ofFibrePt`. The hypothesis `hptsSp₀` pins `ptsSp₀` on differences of $A$-sections: for all $A$-sections $v_1, v_2$ of the level-$\Gamma_N$ model (points over `Spec.map ρ`), all $\kappa$-points $v\kappa_1, v\kappa_2$ of the level-$\Gamma_N$ special fibre whose first projection is the reduction of $v_1$, resp. $v_2$, and whose second projection is the identity, all closed points $Q_1, Q_2$ of the curve model `(𝔛.Mfib A hA ρ hρ).C` with `𝔛.efib` carrying $Q_i$ to the image of the closed point of $\kappa$ under $v\kappa_i$, and every degree-zero divisor $D_w$ equal to the difference of the places of $Q_1$ and $Q_2$ under `(𝔛.Mfib A hA ρ hρ).placeOfPoint`, there exists an $A$-point $s_0$ of `D₀.toBase` such that the pullback along $s_0$ of the Poincaré bundle of `hD₀` is isomorphic to the tensor product of the line bundle (the dual ideal sheaf) of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` of $v_1$ and the ideal sheaf module of that of $v_2$, and such that `ptsSp₀.symm` of the reduction of $s_0$ along `resPt A` is the class of $D_w$.
--
--   Conclusion. There exist a finite set $SS$ of pairs of places of $\bar F$ over $\kappa$, a natural number $t$, a bijection
--   $$\mathrm{ptsSp} : \mathrm{GluedPic}^0(\kappa, \bar F, SS) \;\simeq\; \{\text{points of } D.\mathrm{toBase} \text{ over } \iota\},$$
--   where `GluingData κ F̄ SS` is $\mathrm{Div} \times \mathrm{Div} \times (SS \to \mathrm{Additive}\,\kappa^\times)$, the admissible subgroup consists of those triples whose two divisors have degree zero and whose first (resp. second) divisor vanishes at the first (resp. second) place of each pair in $SS$, and $\mathrm{GluedPic}^0$ is the quotient of the admissible subgroup by the glued principal subgroup; two morphisms $\mathrm{abq}_i$ ($i \in \mathrm{Fin}\,2$) from the base change of `D.toBase` along $\iota$ to the base change of `D₀.toBase` along $\iota$, over $\mathrm{Spec}\,\kappa$; a morphism $\tau$ from the split torus `torusScheme κ t` $= \mathrm{Spec}\,\kappa[\mathbb{Z}^t]$ to the base change of `D.toBase` along $\iota$, over $\mathrm{Spec}\,\kappa$; and a group isomorphism $B$ from the character lattice of $SS$ (the kernel of the sum-of-coordinates map on $SS \to \mathbb{Z}$) onto $\mathrm{Fin}\,t \to \mathbb{Z}$, such that all of the following hold.
--
--   (i) A pair lies in $SS$ if and only if it lies in `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. its second entry is a supersingular place and its first entry is the image of the second under `qExpFrobeniusPlaceModL`.
--
--   (ii) $t + 1 = \#SS$.
--
--   (iii) `ptsSp` is additive for the group law on points over $\iota$ obtained from `hD` by base change along $\iota$ (with `toFibrePt`/`ofFibrePt` as above).
--
--   (iv) For each $i \in \mathrm{Fin}\,2$: given $A$-sections $u_1, u_2$ of the level-$\Gamma_M$ model whose images lie in `𝔛.smoothLocus`, $\kappa$-points $u\kappa_1, u\kappa_2$ of the level-$\Gamma_M$ special fibre whose first projection is the reduction of $u_1$, resp. $u_2$, and whose second projection is the identity, closed points $P_1, P_2$ of `(𝔛.Mfib A hA ρ hρ).C` such that `𝔛.efib` followed by `𝔛.comp i` carries $P_j$ to the image of the closed point of $\kappa$ under $u\kappa_j$, and an admissible gluing datum $x$ whose first component is the difference of the places of $P_1$ and $P_2$ if $i = 0$ and $0$ otherwise, whose second component is that difference if $i = 1$ and $0$ otherwise, and whose third component is $0$: then there exists an $A$-point $s$ of `D.toBase` such that the pullback along $s$ of the Poincaré bundle of `hD` is isomorphic to the tensor product of the line bundle of `RelEffCartierDiv.ofPoint` of $u_1$ with the ideal sheaf module of `RelEffCartierDiv.ofPoint` of $u_2$, and such that `ptsSp.symm` of the reduction of $s$ along `resPt A` is the class of $x$ in $\mathrm{GluedPic}^0$.
--
--   (v) Each $\mathrm{abq}_i$ is multiplicative: for every scheme $T$, every $s : T \to \mathrm{Spec}\,\kappa$ and all points $x, y$ of the base change of `D.toBase` over $s$, composing the product of $x$ and $y$ with $\mathrm{abq}_i$ equals the product, in the base-changed group law coming from `hD₀`, of the composites of $x$ and of $y$ with $\mathrm{abq}_i$.
--
--   (vi) The morphism `pullback.lift (abq 0).1 (abq 1).1 …` into the fibre product of the two copies of the base change of `D₀.toBase` is flat and surjective.
--
--   (vii) For every scheme $T$, every $s : T \to \mathrm{Spec}\,\kappa$ and every point $x$ of the base change of `D.toBase` over $s$: the composites of $x$ with $\mathrm{abq}_0$ and with $\mathrm{abq}_1$ are both the neutral element if and only if $x$ factors as some point $y$ of the split torus `torusStr κ t` over $s$ followed by $\tau$.
--
--   (viii) For every endomorphism $\sigma$ of $\mathrm{Spec}\,\kappa$ over $\iota$ (a point of $\iota$ over $\iota$), every $i$ and every point $x$ of `D.toBase` over $\iota$, the map `fibreMap (abq i)` commutes with precomposition by $\sigma$.
--
--   (ix) For every $x \in \mathrm{GluedPic}^0(\kappa, \bar F, SS)$ and every $i$: `ptsSp₀.symm (fibreMap (abq i) (ptsSp x))` is the first component of `GluedPic0.toPic0Pair SS x` when $i = 0$ and its second component when $i = 1$; that is, $\mathrm{abq}_i$ read through the two dictionaries is the passage from a glued class to the $\mathrm{Pic}^0$ class of its $i$-th divisor.
--
--   (x) The underlying morphism of $\tau$ is a closed immersion.
--
--   (xi) $\tau$ is multiplicative on torus points: for all $\chi, \chi'$ in `WithConv` of the set of $\kappa$-algebra maps `torusCoord κ t →ₐ[κ] κ` (a type carrying a product, written $\chi \chi'$, with `ofConv` recovering the underlying algebra map), the torus point attached to $\chi\chi'$ followed by $\tau$ equals the product, in the base-changed group law from `hD`, of the torus point of $\chi$ followed by $\tau$ and the torus point of $\chi'$ followed by $\tau$.
--
--   (xii) For every $x \in \mathrm{GluedPic}^0(\kappa, \bar F, SS)$: `toFibrePt (ptsSp x)` factors as a $\kappa$-point of the split torus followed by $\tau$ if and only if $x$ lies in the image of `GluedPic0.nodeUnit SS`, the homomorphism sending $w : SS \to \mathrm{Additive}\,\kappa^\times$ to the class of $(0, 0, w)$.
--
--   (xiii) Torus coordinates: for every $\kappa$-algebra map $\chi : \kappa[\mathbb{Z}^t] \to \kappa$ and every $w : SS \to \mathrm{Additive}\,\kappa^\times$, the torus point of $\chi$ followed by $\tau$ equals `toFibrePt (ptsSp (GluedPic0.nodeUnit SS w))` if and only if for every $a$ in the character lattice of $SS$ one has $\prod_{s \in SS} (\mathrm{toMul}\,w(s))^{a(s)} = \chi(\text{monomial } B(a))$ in $\kappa$.
--
--   This is the special-fibre half of the Deligne–Rapoport–Raynaud description, at a prime $p$ with $p \,\|\, M$, of the relative $\mathrm{Pic}^0$ of the integral model of $X_H(M)$: its $\kappa$-points are identified with the glued degree-zero divisor classes of the level-$\Gamma_N$ curve over $\kappa$, the two projections to the $\kappa$-points of the level-$\Gamma_N$ $\mathrm{Pic}^0$ are exhibited as a jointly flat and surjective pair of homomorphisms, and the kernel is exhibited as a split torus of rank $\#SS - 1$, closed-immersed and with its character coordinates matched to the node units indexed by the supersingular pairs. It feeds the construction of the Néron-model package at $p$ for $J_H(M)$, being cited by [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_ptsSp_gluedPic0_dictionary_specialFibre.lean

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

theorem ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]
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
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw) :
    ∃ (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
      (t : ℕ)
      (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
        SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
      (abq : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase))
      (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase))
      (B : characterLattice ↥SS ≃+ (Fin t → ℤ)),

      (∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p) ∧
      t + 1 = SS.card ∧

      (∀ x y, ptsSp (x + y) =
        ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
          (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y)))) ∧

      (∀ (i : Fin 2)
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
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)),
        NeronModelInfra.schemeHomOverComp (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul s x y) (abq i) =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul s
            (NeronModelInfra.schemeHomOverComp x (abq i)) (NeronModelInfra.schemeHomOverComp y (abq i))) ∧
      Flat (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧
      Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)),
        (∀ i, NeronModelInfra.schemeHomOverComp x (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).one s) ↔
          ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) t), NeronModelInfra.schemeHomOverComp y τ = x) ∧
      (∀ (σ : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))) (i : Fin 2)
        (x : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        fibreMap (abq i) (GoodReductionJacobian.schemeHomOverComp σ.1 σ.2 x) =
          GoodReductionJacobian.schemeHomOverComp σ.1 σ.2 (fibreMap (abq i) x)) ∧

      (∀ (x : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS) (i : Fin 2),
        ptsSp₀.symm (fibreMap (abq i) (ptsSp x)) =
          if i = 0 then (GluedPic0.toPic0Pair SS x).1 else (GluedPic0.toPic0Pair SS x).2) ∧

      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A),
        NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
            (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ)) ∧
      (∀ x : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS,
        (∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) t),
            NeronModelInfra.schemeHomOverComp y τ = toFibrePt (ptsSp x)) ↔
          x ∈ (GluedPic0.nodeUnit SS).range) ∧

      (∀ (χ : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A)
          (w : ↥SS → Additive (ResidueField ↥A)ˣ),
        NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) t χ) τ =
            toFibrePt (ptsSp (GluedPic0.nodeUnit SS w)) ↔
          ∀ a : characterLattice ↥SS,
            ((∏ s, Additive.toMul (w s) ^ (a : ↥SS → ℤ) s : (ResidueField ↥A)ˣ) : ResidueField ↥A) =
              χ (AddMonoidAlgebra.single (B a) 1)) := by sorry

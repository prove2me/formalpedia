-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/192629e0-7ded-50a6-8427-f1d3ac67b8d7
-- title:
--   Matching the generic and special Pic⁰ dictionaries by an A-section
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤` of full-level modular functions over $\mathbb{Q}$, so that the two-chart integral models `toBase p Γ hj : X p Γ hj ⟶ Spec (R p)` are available. Let $\mathfrak{X}$ be a datum of type `XHDRModelAtP p M H hpM hj`, which packages the integral model `toBase p (ΓM M H) hj` of the level-$\Gamma_M(H)$ modular curve over $R_p$ together with its section `𝔛.εinf` over `Spec (R p)`, the open set `𝔛.smoothLocus`, the curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ of the function field `xHFunctionFieldBar M H` and the isomorphism `𝔛.eeta` of `𝔛.Meta.C` with the geometric generic fibre `pullback (toBase p (ΓM M H) hj) (genPt p)`, and the special-fibre data `𝔛.Mfib`, `𝔛.efib`, `𝔛.comp` indexed by `Fin 2`.
--
--   Valuation-theoretic data: $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed; and $\rho : R_p \to A$ is a ring homomorphism with `hρ` asserting that composing $\rho$ with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$. The model and its base change to $\mathbb{Q}$ are assumed separated over their bases.
--
--   Representability data: $D$ is a `RelativePic0Designation` for `toBase p (ΓM M H) hj` over $R_p$, that is a scheme `D.P` over `Spec (R p)` with a zero section; `hD` asserts that $D$ represents the subfunctor of rigidified line bundles on the model (rigidified along `𝔛.εinf`) cut out by the condition `FibrewiseAlgEquivZero` of `algEquivZeroCut`: there is a Poincaré bundle `hD.poincare` on `D.toBase` satisfying the condition, every such rigidified bundle over a base $T \to \operatorname{Spec} R_p$ comes from a unique section $T \to$ `D.P` over `Spec (R p)` up to isomorphism of the pullbacks, and the pullback along the zero section is trivial. The hypothesis `hDQ` asserts the same representability over $\mathbb{Q}$, for the base-changed curve `baseChange (R p) (toBase p (ΓM M H) hj) ℚ`, the base-changed section `sectionBaseChange ℚ 𝔛.εinf` and the designation `D.baseChange ℚ` obtained by pulling `D.P` back along $\operatorname{Spec}\mathbb{Q} \to \operatorname{Spec}R_p$.
--
--   Abel–Jacobi data over $\mathbb{Q}$ (the group `ajQ`, `kQ`, `ajbar`, `hPQ`, `hajε`, `hajcl`, `hkQ₁`, `hkQ₂`, `hajbar`): `ajQ` is a morphism from the $\mathbb{Q}$-fibre of the model to `(D.baseChange ℚ).P` commuting with the maps to $\operatorname{Spec}\mathbb{Q}$; `kQ` is a morphism from the geometric generic fibre to the $\mathbb{Q}$-fibre, compatible with the first projections (`hkQ₁`) and inducing $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$ on the second projections (`hkQ₂`); `ajbar : 𝔛.Meta.C ⟶ D.P` is pinned by `hajbar` to be `𝔛.eeta` followed by `kQ`, then by `ajQ.1`, then by `pullback.fst D.toBase (specMap (R p) ℚ)`. The hypothesis `hPQ` says that `hDQ.poincare` is isomorphic to the bundle obtained by `BaseChange.ofR` from the pullback of `hD.poincare` along the first projection of `pullback D.toBase (specMap (R p) ℚ)`. The hypothesis `hajε` says that `sectionBaseChange ℚ 𝔛.εinf` followed by `ajQ.1` is the zero section of `D.baseChange ℚ`. The hypothesis `hajcl` says that for every field $K$, every $t : \operatorname{Spec}K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the $\mathbb{Q}$-fibre over $t$, the pullback of `hDQ.poincare` along $x$ followed by `ajQ` is isomorphic to the tensor product of the line bundle of the degree-one relative effective Cartier divisor `RelEffCartierDiv.ofPoint` cut out by $x$ with the ideal-sheaf module of the divisor cut out by the $\infty$-section over $t$.
--
--   Generic dictionary: `pts` is a bijection from $J_H(M) =$ `Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)` (degree-zero divisors of the function field modulo principal ones) onto the sections of `D.toBase` over `genPt p`; `hpts_law` says `pts` is additive for the relative group law that `hD` (through `algEquivZeroGroupCut`) puts on `D.toBase`; and `hAJ` says that for all $\overline{\mathbb{Q}}$-points $x, s$ of `𝔛.Meta.C` over $\operatorname{Spec}\overline{\mathbb{Q}}$ such that $s$ followed by `𝔛.eeta` and the first projection equals `genPt p ≫ 𝔛.εinf.1`, there is a degree-zero divisor $D_v$ with underlying divisor $[\,\text{place of }x\,] - [\,\text{place of }s\,]$ (via `𝔛.Meta.pointEquivPlace`) such that `(pts (Pic0.mk Dv)).1` equals $x$ followed by `ajbar`.
--
--   Special-fibre dictionary: `SS` is a finite set of pairs of places of `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$; `ptsSp` is a bijection from `GluedPic0 κ (Fbar …) SS`, the quotient of the group of admissible gluing data — triples consisting of two divisors of degree zero, vanishing at the first, respectively second, members of the pairs in `SS`, together with a family of units indexed by `SS` — by the glued principal data, onto the sections of `D.toBase` over `resPt A ≫ Spec.map ρ`. The hypothesis `hPTSDIV` is the divisor pin for `ptsSp`: for every $i \in \{0,1\}$, every $A$-section $u_1$ of the model (over $\operatorname{Spec}\rho$) whose image lies in `𝔛.smoothLocus`, every $\kappa$-point $u\kappa_1$ of the fibre over $\kappa$ that is a section of it and is the reduction of $u_1$, every closed point $P_1$ of `(𝔛.Mfib A hA ρ hρ).C` mapping under `𝔛.efib ≫ 𝔛.comp … i` to the underlying point of $u\kappa_1$, the same data $u_2, u\kappa_2, P_2$, and every admissible gluing datum $x$ whose first component is $[P_1]-[P_2]$ (in the places `placeOfPoint` of `𝔛.Mfib`) if $i = 0$ and $0$ otherwise, whose second component is $[P_1]-[P_2]$ if $i = 1$ and $0$ otherwise, and whose unit component is trivial, there exists a section $s$ of `D.toBase` over $\operatorname{Spec}\rho$ such that the pullback of `hD.poincare` along $s$ is isomorphic to the tensor product of the line bundle of the divisor of $u_1$ with the ideal-sheaf module of the divisor of $u_2$, and `ptsSp.symm` of the $\kappa$-point obtained by composing `resPt A` with $s$ is the class `GluedPic0.mk SS x`.
--
--   Under these hypotheses, the following holds. Let $i \in \{0,1\}$. Let $y_1$ be a $\overline{\mathbb{Q}}$-point of `𝔛.Meta.C` over $\operatorname{Spec}\overline{\mathbb{Q}}$, let $u_1$ be an $A$-section of the model over $\operatorname{Spec}\rho$ with `barPt A ≫ u₁.1` equal to $y_1$ followed by `𝔛.eeta` and the first projection, and with the image of $u_1$ contained in `𝔛.smoothLocus`; let $u\kappa_1$ be a $\kappa$-point of the fibre over $(\mathrm{residue}\circ\rho)$ which is a section of that fibre and whose composition with the first projection is the reduction of $u_1$; and let $P_1$ be a closed point of `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib ≫ 𝔛.comp … i` is the underlying point of $u\kappa_1$ at the closed point of $\kappa$. Let $y_2, u_2, u\kappa_2, P_2$ be a second such family, subject to the same five conditions. Let $D_v$ be a degree-zero divisor of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ whose underlying divisor is $[\,\text{place of }y_1\,] - [\,\text{place of }y_2\,]$, and let $x$ be an admissible gluing datum for `SS` whose first component is $[P_1]-[P_2]$ if $i = 0$ and $0$ otherwise, whose second component is $[P_1]-[P_2]$ if $i = 1$ and $0$ otherwise, and whose unit component is trivial. Then there exists a section $s$ of `D.toBase` over $\operatorname{Spec}\rho$ such that both
--
--   (i) `(pts (Pic0.mk Dv)).1` equals `barPt A` followed by $s$, and
--
--   (ii) `ptsSp.symm` of the $\kappa$-point obtained by composing `resPt A` with $s$ equals `GluedPic0.mk SS x`.
--
--   Thus the conclusion, unlike `hPTSDIV`, identifies the generic value of the $A$-section with the image under the generic dictionary of the class of $[y_1]-[y_2]$, in place of the line-bundle description of $s$.
--
--   This is the compatibility statement between the Abel–Jacobi-normalised generic dictionary on $J_H(M)(\overline{\mathbb{Q}})$ and the dictionary for the glued $\mathrm{Pic}^0$ of the special fibre at $p$ of the Deligne–Rapoport-type model at level $\Gamma_H(M)$: a degree-zero class $[y_1]-[y_2]$ coming from $\overline{\mathbb{Q}}$-points that extend to $A$-sections in the smooth locus reducing onto one and the same component has an $A$-valued point of the relative $\mathrm{Pic}^0$ whose reduction is the expected glued class. It is used in assembling the Néron-type object at $p$ in [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords) and in [`ModularCurve.XHDRModelAtP.ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp`](thm.html#ModularCurve.XHDRModelAtP.ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent.lean

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

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_eq_and_ptsSp_symm_eq_mk_of_sameComponent
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ D.P)
    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hpts_law : ∀ x y : JH M H,
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hAJ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
        SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hPTSDIV : ∀ (i : Fin 2)
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
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x) :
    (∀ (i : Fin 2)
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
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        (pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x) := by sorry

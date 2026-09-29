-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
-- name    : ModularCurve.JHNeronObjectAtP.exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/54ed2394-e35e-5f6d-9f8f-f39743d51bcc
-- title:
--   Presentation divisor of σ^*P is D' up to principal divisors
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^{2} \nmid M$, and a subgroup $H \le (\mathbb Z/M)^{\times}$ containing every unit whose image in $(\mathbb Z/(M/p))^{\times}$ is $1$. Let $Pl$ be a valuation subring of $\overline{\mathbb Q}$ in which $p$ is a nonunit, with algebraically closed residue field of characteristic $p$, and assume the $q$-expansion `jqModC` of $j$ lies in the level-$\mathrm{SL}(2,\mathbb Z)$ $q$-expansion function field over $\mathbb Q$. Let $\mathfrak X$ be an `XHDRModelAtP` datum for $(p,M,H)$, so in particular an integral model $X \to \operatorname{Spec} R_p$ of the modular curve of level $\Gamma_H(M)$ together with a curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ whose function field is identified with $\bar F_H(M)$ by `ffEquiv`; let $\Lambda$ be level data and $O$ a Néron object at $Pl$, with total space $O.G \to \operatorname{Spec} R_p$, relative group law $O.L$ and bijection $\mathrm{pts} : J_H(M) \simeq$ {sections of $O.g$ over the geometric generic point}. The hypotheses of representability and Abel–Jacobi type, summarised here, are: `hD`, that the designation formed from $O.G$, $O.g$ and the unit section represents the relative Picard functor of $X \to \operatorname{Spec} R_p$ rigidified along $\mathfrak X.\varepsilon_{\inf}$ and cut out by fibrewise algebraic triviality, with Poincaré bundle $\mathcal P$; `hDQ`, the same after base change to $\mathbb Q$; separatedness of the $\mathbb Q$-fibre; a morphism $aj_{\mathbb Q}$ over the $\mathbb Q$-designation carrying the rigidifying section to the zero section, such that for every field $K$, every $K$-point $t$ of $\operatorname{Spec}\mathbb Q$ and every $t$-point $x$ of the $\mathbb Q$-fibre the pullback of the $\mathbb Q$-Poincaré bundle along $x$ followed by $aj_{\mathbb Q}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of $t$ followed by the rigidifying section; an isomorphism between the $\mathbb Q$-Poincaré bundle and the base change to $\mathbb Q$ of the pullback of $\mathcal P$; a morphism $k_{\mathbb Q}$ between the two fibre products compatible with both projections; a morphism $\overline{aj} : \mathfrak X.\mathrm{Meta}.C \to O.G$ defined as $\mathfrak X.\mathrm{eeta}$ followed by $k_{\mathbb Q}$, $aj_{\mathbb Q}$ and the first projection, lying over the geometric generic point; a geometric point $\bar\varepsilon$ of $\mathfrak X.\mathrm{Meta}.C$ lying over $\mathfrak X.\varepsilon_{\inf}$ and sent by $\overline{aj}$ to the identity section; additivity of $\mathrm{pts}$ for the group law supplied by `hD`; and the property that for all geometric points $x,s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ lying over $\mathfrak X.\varepsilon_{\inf}$ there is a degree-zero divisor equal to $[v_x] - [v_s]$, in the places attached to $x$ and $s$, whose class has $\mathrm{pts}$ equal to $x$ followed by $\overline{aj}$. Further let $\rho : R_p \to Pl$ be a ring homomorphism whose composite with the inclusion of $Pl$ is the structure map $R_p \to \overline{\mathbb Q}$, and $g_A : \mathfrak X.\mathrm{Meta}.C \to X \times_{R_p} \operatorname{Spec} Pl$ an open immersion compatible with the first projection via $\mathfrak X.\mathrm{eeta}$ and lying over `barPt` $Pl$, the target being integral. Let $z \in J_H(M)$ be the class of a degree-zero divisor $D'$ on $\bar F_H(M)$, and $\sigma$ a section of $O.g$ over $\operatorname{Spec} Pl$ whose restriction along `barPt` is $\mathrm{pts}(z)$. Finally let $D_1$ be a divisor on $\mathfrak X.\mathrm{Meta}.C$'s function field over $\overline{\mathbb Q}$ and, for each open $V$, let $\varphi_1(V)$ be an additive map from the sections over $V$ of the restriction along $g_A$ of the line bundle $(\sigma^{*}\mathcal P).L$ to the function field, such that the $\varphi_1$ commute with restriction to nonempty smaller opens, satisfy $\varphi_1(a \cdot m) = a \cdot \varphi_1(m)$ for $a$ a section of the structure sheaf, are injective over nonempty opens, and have range over each nonempty affine open $U$ equal to the space of functions $f$ with $v(f) \le \exp(D_1(v))$ for every place $v$ arising from a closed point of $U$. Then there is a nonzero element $g_2$ of the function field such that for every place $v$ of $\bar F_H(M)$ one has $D_1(v') = D'(v) + \mathrm{ord}_{v'}(g_2)$, where $v'$ is the transport of $v$ along `ffEquiv`.
--
--   This is the comparison, on the geometric generic fibre, between the Riemann–Roch divisor read off from an arbitrary presentation of the pullback of the Poincaré bundle along a $Pl$-valued section of the Néron object and a degree-zero divisor representing the corresponding class: the two agree up to the divisor of a single nonzero function, so $\sigma^{*}\mathcal P$ restricted to the generic fibre is $\mathcal O(D')$ up to linear equivalence. It feeds the construction of divisor-level presentations of $\sigma^{*}\mathcal P$ used in the study of the Néron model of $J_H(M)$ at $p$, being cited by [`ModularCurve.JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts`](thm.html#ModularCurve.JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 800000 in
open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    [hint : IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]

    (z : ModularCurve.JH M H)
    (D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hD' : AlgebraicCurve.Pic0.mk D' = z)
    (σ : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g)
    (hσ : ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ σ.1 = (O.pts z).1)
    [hgAo : IsOpenImmersion gA]
    (D₁ : letI := 𝔛.Meta.functionFieldAlgebra
      AlgebraicCurve.Divisor (AlgebraicClosure ℚ) 𝔛.Meta.C.functionField)
    (φ₁ : ∀ V : 𝔛.Meta.C.Opens, Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, V) →+ (𝔛.Meta.C.functionField : Type))
    (h1nat : ∀ (U V : 𝔛.Meta.C.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, U),
        φ₁ V ((((hD.poincare.pullbackAlong σ).L).restrict gA).presheaf.map (homOfLE h).op m) = φ₁ U m)
    (h1smul : ∀ (U : 𝔛.Meta.C.Opens) [Nonempty U] (a : Γ(𝔛.Meta.C, U)) (m : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, U)),
      φ₁ U (a • m) = algebraMap Γ(𝔛.Meta.C, U) 𝔛.Meta.C.functionField a * φ₁ U m)
    (h1inj : ∀ U : 𝔛.Meta.C.Opens, Nonempty U → Function.Injective (φ₁ U))
    (h1range : letI := 𝔛.Meta.functionFieldAlgebra
      ∀ U : 𝔛.Meta.C.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ₁ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf 𝔛.Meta.toBase U) D₁ : Set 𝔛.Meta.C.functionField)) :
    letI := 𝔛.Meta.functionFieldAlgebra
    ∃ g₂ : 𝔛.Meta.C.functionField, g₂ ≠ 0 ∧
      ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        D₁ (AlgebraicCurve.Place.congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v) =
          (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v +
          (AlgebraicCurve.Place.congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v).ord g₂ := by sorry

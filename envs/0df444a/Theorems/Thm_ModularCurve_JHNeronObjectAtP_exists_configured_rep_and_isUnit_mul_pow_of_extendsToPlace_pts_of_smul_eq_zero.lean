-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero
-- name    : ModularCurve.JHNeronObjectAtP.exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/57078f96-e81c-5d5a-85dc-a6b2282d08cc
-- title:
--   Configured representative of a p-torsion class extending at P
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb Z/M)^\times$ which, by `hHp`, contains every unit killed by the reduction map `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)` to $(\mathbb Z/(M/p))^\times$. Fix a valuation subring $\mathrm{Pl}$ of $\overline{\mathbb Q}$ lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16) (that is, $p$ is a non-unit of $\mathrm{Pl}$), whose residue field $\kappa = \mathrm{ResidueField}\ \mathrm{Pl}$ has characteristic $p$ and is algebraically closed. The hypothesis `hj` states that the $q$-expansion `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤`, so that the two-chart integral models `X p Γ hj` and their structure morphisms `toBase p Γ hj` over the base ring `R p` are available.
--
--   The geometric data are: an integral model $\mathfrak X$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) for the curve of level $\Gamma_H(M)$, carrying among its fields a curve model `𝔛.Meta` of the geometric function field `xHFunctionFieldBar M H`, an isomorphism `𝔛.eeta` of `𝔛.Meta.C` with the base change of `X p (ΓM M H) hj` to $\overline{\mathbb Q}$, the cusp section `𝔛.εinf`, the smooth locus `𝔛.smoothLocus`, and the special-fibre data `𝔛.Mfib`, `𝔛.efib`, `𝔛.comp` indexed by `Fin 2`; level data $\Lambda$ of type `LevelData p M H hpM Pl`; and a Néron object $O$ of type `JHNeronObjectAtP p M H hpM Pl hPl Λ`, with total space `O.G`, structure morphism `O.g` over `base p`, relative group law `O.L`, and bijection `O.pts : JH M H ≃ SchemeHomOver (genPt p) O.g`.
--
--   The representability group consists of: `hD`, asserting that the designation $(O.G, O.g, (O.L.one (𝟙 \_)).1)$ of type `RelativePic0Designation (R p) (toBase p (ΓM M H) hj)` represents the rigidified relative Picard functor of `toBase p (ΓM M H) hj` with zero section `𝔛.εinf` in the cut `algEquivZeroCut` (fibrewise algebraic triviality); `hDQ`, the same statement for the base change to $\mathbb Q$ of all these data; and `hsep`, separatedness of `baseChange (R p) (toBase p (ΓM M H) hj) ℚ`, which allows relative effective Cartier divisors of points to be formed.
--
--   The Abel–Jacobi group consists of: a morphism `ajQ` from the generic fibre over $\mathbb Q$ to the base-changed designation, over $\operatorname{Spec}\mathbb Q$; a morphism `kQ` from `pullback (toBase …) (genPt p)` to `pullback (toBase …) (specMap (R p) ℚ)` compatible with the two projections by `hkQ₁` and by `hkQ₂` (the second projection followed by `specMap ℚ (AlgebraicClosure ℚ)`); the morphism `ajbar : 𝔛.Meta.C ⟶ O.G`, defined by `hajbar` to be `𝔛.eeta` followed by `kQ`, `ajQ.1` and `pullback.fst O.g (specMap (R p) ℚ)`, and lying over `genPt p` by `hajbar_over`; a $\overline{\mathbb Q}$-point `εbar` of `𝔛.Meta.C` which by `hεbar` is the cusp `𝔛.εinf` and which by `hεbar_aj` is sent by `ajbar` to the unit section; `hpoinc`, an isomorphism between the Poincaré bundle of `hDQ` and the bundle obtained from that of `hD` by pulling back along `⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩` and applying `BaseChange.ofR`; `hajQε`, saying that the cusp section composed with `ajQ` is the zero section of the base-changed designation; `hajQ`, saying that for every field $K$, every morphism $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of the generic fibre over $t$, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by `ajQ` is isomorphic to the line bundle of the divisor of the point $x$ tensored with the ideal module of the divisor of the cusp point $t$ followed by the base-changed `𝔛.εinf`; `hpts_law`, that `O.pts` is additive for the relative group law `RepresentsRelSubPic.relativeGroupLaw` attached to `hD` in the cut `algEquivZeroGroupCut`; and `hAJ`, that for all $\overline{\mathbb Q}$-points $x, s$ of `𝔛.Meta.C` with $s$ equal to the cusp, there is a degree-zero divisor $D_v$ equal to $\mathrm{single}(\text{place of }x) - \mathrm{single}(\text{place of }s)$ under `𝔛.Meta.pointEquivPlace` with $(O.\mathrm{pts}\,[D_v]).1 = x$ followed by `ajbar`.
--
--   The place-theoretic group consists of: a ring homomorphism $\rho :$ `R p` $\to \mathrm{Pl}$ with `hρ` saying that $\rho$ followed by the inclusion of $\mathrm{Pl}$ is the structure map to $\overline{\mathbb Q}$, and `hσA` identifying `Λ.σA` with `Spec.map (CommRingCat.ofHom ρ)`; a morphism `gA` from `𝔛.Meta.C` to `pullback (toBase …) (Spec.map (CommRingCat.ofHom ρ))` whose compositions with the projections are prescribed by `hgA₁` (`𝔛.eeta` followed by the first projection) and `hgA₂` (`𝔛.Meta.toBase` followed by `barPt Pl`); and a morphism `bc` from the fibre `fibre ((IsLocalRing.residue Pl).comp ρ)` to the same pullback, compatible with the projections by `hbc₁` and `hbc₂` (the second projection followed by `Spec.map` of the residue map).
--
--   Finally, the torsion datum: a class $z \in$ `JH M H` whose Néron point `O.pts z` satisfies `ExtendsToPlace Pl Λ.σA`, i.e. factors as `barPt Pl` followed by a section of `O.g` over `Λ.σA` (`hz`), with $p \cdot z = 0$ (`hpz`); a degree-zero divisor $D'$ on the geometric function field `xHFunctionFieldBar M H` with $[D'] = z$ (`hD'`); a non-zero function $f$ of that field with $p \cdot D'(v) = v.\mathrm{ord}\, f$ at every place $v$ (`hdiv`); and a Laurent series $y$ over $\mathrm{Pl}$ with `coeffMap Pl.subtype y` equal to the Laurent series of $f$ (`hfy`) and with non-zero reduction `coeffMap (IsLocalRing.residue Pl) y` (`hy`).
--
--   Under these hypotheses there exist: a function $h$ of `xHFunctionFieldBar M H`; Laurent series $x_h, y_h$ over $\mathrm{Pl}$; an element $\bar h$ of `Fbar p M H hpM κ`, that is of the field `qExpFunctionFieldC κ (ΓN p M H hpM)`; a natural number $k$; a component index $c : \mathrm{Fin}\,k \to \mathrm{Fin}\,2$; $\overline{\mathbb Q}$-points $y_v(i)$ of `𝔛.Meta.C`; $\mathrm{Pl}$-points $u(i)$ of `toBase p (ΓM M H) hj` over `Spec.map (CommRingCat.ofHom ρ)`; $\kappa$-points $u_\kappa(i)$ of the fibre `fibre ((IsLocalRing.residue Pl).comp ρ)`; closed points $P(i)$ of `(𝔛.Mfib Pl hPl ρ hρ).C`; integers $n(i)$; and a degree-zero divisor $D_v$, such that all of the following hold.
--
--   First, $h \neq 0$, the reductions `coeffMap (IsLocalRing.residue Pl) xh` and `coeffMap (IsLocalRing.residue Pl) yh` are both non-zero, the Laurent series of $h$ over $\overline{\mathbb Q}$ times `coeffMap Pl.subtype yh` equals `coeffMap Pl.subtype xh`, and the Laurent series of $\bar h$ over $\kappa$ times the reduction of $y_h$ equals the reduction of $x_h$; thus $h$ is presented as the ratio $x_h/y_h$ of $\mathrm{Pl}$-integral series and $\bar h$ as the ratio of their reductions.
--
--   Second, for every $i$: `barPt Pl` followed by $u(i)$ equals $y_v(i)$ followed by `𝔛.eeta` and the first projection, so $u(i)$ extends the geometric point $y_v(i)$; the set-theoretic image of $u(i)$ is contained in `𝔛.smoothLocus`; $u_\kappa(i)$ followed by the first projection equals `Spec.map` of the residue map followed by $u(i)$, and $u_\kappa(i)$ followed by the second projection is the identity, so $u_\kappa(i)$ is the reduction of $u(i)$; and the closed point $P(i)$ is carried by `𝔛.efib Pl hPl ρ hρ` followed by `𝔛.comp Pl hPl ρ hρ (c i)` to the image under $u_\kappa(i)$ of the closed point of $\kappa$.
--
--   Third, $D_v = \sum_i n(i) \cdot \mathrm{single}(\text{place of } y_v(i))$, the places being taken through `𝔛.Meta.pointEquivPlace`, and $D_v(v) = D'(v) + v.\mathrm{ord}\,h$ at every place $v$; so $D_v$ is a representative of $z$ supported at the places of the chosen points.
--
--   Fourth, for every closed point $\bar P$ of `(𝔛.Mfib Pl hPl ρ hρ).C` whose place `(𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P̄` lies in `ssPlacesQExp κ (ΓN p M H hpM) p`, there are an open subset $U$ of `pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))` containing the image under `bc` of the point obtained from $\bar P$ by `𝔛.efib Pl hPl ρ hρ` followed by `𝔛.comp Pl hPl ρ hρ 0`, a proof that the preimage `gA ⁻¹ᵁ U` is non-empty, and a section $s \in \Gamma(U)$ such that $s$ is a unit and the function of `xHFunctionFieldBar M H` obtained from $s$ by pulling back along `gA`, taking the germ at the function field of `𝔛.Meta.C` and transporting through `𝔛.Meta.ffEquiv.symm`, equals $f \cdot h^{p}$.
--
--   This is the geometric core of the argument at a prime exactly dividing the level: a $p$-torsion class whose Néron point extends over the place $\mathfrak P$ is given a divisor representative supported at points that extend to sections through the smooth locus, together with a function $h$ for which $f h^{p}$ is a unit in a neighbourhood of each supersingular crossing of the special fibre. It feeds the companion statement [`ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero`](thm.html#ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero), which converts the unit conclusion into a statement about orders of vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 800000 in
open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
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
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (z : ModularCurve.JH M H)
    (hz : ExtendsToPlace Pl Λ.σA (O.pts z))
    (hpz : p • z = 0)
    (D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hD' : AlgebraicCurve.Pic0.mk D' = z)
    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdiv : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v = v.ord f)
    (y : LaurentSeries ↥Pl)
    (hfy : (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y)
    (hy : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0) :
    ∃ (h : ↥(ModularCurve.xHFunctionFieldBar M H)) (xh yh : LaurentSeries ↥Pl) (hbar : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
        (k : ℕ) (c : Fin k → Fin 2)
        (yv : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : Fin k → NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uκ : Fin k → (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
        (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
        (n : Fin k → ℤ)
        (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),

        h ≠ 0 ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ≠ 0 ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh ≠ 0 ∧
        (h : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype yh = ModularCurve.coeffMap Pl.subtype xh ∧
        (hbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ∧

        (∀ i, ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ (u i).1 = (yv i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ∧
        (∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
        (∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u i).1) ∧
        (∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _) ∧
        (∀ i, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥Pl))) ∧
        ((Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
          ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (yv i)) 1) ∧

        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v =
            (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord h) ∧

        (∀ Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
          (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∈
            ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
            (_ : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
            (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
            (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
            IsUnit s ∧
            𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) = f * h ^ p) := by sorry

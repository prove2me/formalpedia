-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_degeneracyHom_mul_pts_special
-- name    : ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/87a51008-34de-53c0-a35d-6fca6adb653f
-- title:
--   Degeneracy morphisms D → D₀ and Ribet's special-fibre formula
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$ (`hHp`), and the hypothesis `hj` that the $q$-series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport-style integral model datum for $X_H(M)$ over $R_p$ together with its generic curve model `𝔛.Meta` for the function field $\bar F_{M,H} =$ `xHFunctionFieldBar M H`, the isomorphism `𝔛.eeta` identifying `𝔛.Meta.C` with the base change of `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbb{Q}}$, the Atkin–Lehner involution `𝔛.w`, the degeneracy morphism `𝔛.π` to level `ΓN p M H hpM`, the rigidifying section `𝔛.εinf`, and the special-fibre data `𝔛.Mfib`, `𝔛.efib`, `𝔛.comp` at a valuation subring; properness of `toBase p (ΓM M H) hj` and of `toBase p (ΓN p M H hpM) hj`, separatedness of both, are assumed as instances.
--
--   The remaining data split into the following blocks, all of which are hypotheses of the theorem.
--
--   *Atkin–Lehner on $q$-expansions* (`θ`, `hθ`): an automorphism $\theta$ of $\bar F_{M,H}$ over $\overline{\mathbb{Q}}$ which, on every element of $\bar F_{M,H}$ that agrees as a Laurent series with an element $u$ of `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, returns `qExpand _ p` applied to that Laurent series; and `hwgen`, stating that for $\overline{\mathbb{Q}}$-points $y, y'$ of `𝔛.Meta.C` over the base, if $y'$ followed by `𝔛.eeta`, the first projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, then `𝔛.Meta.pointEquivPlace y'` is the translate of `𝔛.Meta.pointEquivPlace y` by the semilinear automorphism `SemilinearAut.ofAlgAut θ`.
--
--   *The relative $\mathrm{Pic}^0$ at level $\Gamma_M$* : a designation $D$ of a relative $\mathrm{Pic}^0$ for `toBase p (ΓM M H) hj` over $R_p$ (a scheme with a structure morphism to $\operatorname{Spec} R_p$ and a zero section), together with `hD` asserting that $D$ represents the functor of `𝔛.εinf`-rigidified line bundles satisfying the fibrewise algebraically-trivial condition `algEquivZeroCut`, with its Poincaré bundle and universal property; and the geometric properties `hsm`, `hsep`, `hqc`, `hsurj`, `hgc` of `D.toBase` (smooth, separated, quasi-compact, surjective, geometrically connected).
--
--   *Generic Abel–Jacobi block at level $\Gamma_M$* (`hDQ`, `hPQ`, `ajQ`, `hajQε`, `hajQ`, `kQ`, `hkQ₁`, `hkQ₂`, `ajbar`, `hajbar`, `hajbar_over`, `εbar`, `hεbar`, `hεbar_aj`): the base change of $D$ to $\mathbb{Q}$ represents the corresponding rigidified relative $\mathrm{Pic}^0$ over $\mathbb{Q}$, its Poincaré bundle is isomorphic to the base change of the one over $R_p$; $ajQ$ is a morphism over $\mathbb{Q}$ from the base-changed curve to the base-changed $D$ sending the section to the zero section and classifying, for every field $K$ and $K$-point $x$, the line bundle $\mathcal{O}(x) \otimes I_{\varepsilon_\infty}$; $kQ$ is the comparison morphism between the fibres over $\overline{\mathbb{Q}}$ and over $\mathbb{Q}$ with its two compatibilities; `ajbar` is the resulting Abel–Jacobi morphism `𝔛.Meta.C ⟶ D.P` over `genPt p`; and `εbar` is a $\overline{\mathbb{Q}}$-point of `𝔛.Meta.C` lying over `𝔛.εinf` and sent by `ajbar` to the zero section.
--
--   *Points dictionary at level $\Gamma_M$* (`pts`, `hpts_add`, `hpts_galois`, `hpts_aj`): a bijection `pts` between $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \bar F_{M,H})$ and the $\overline{\mathbb{Q}}$-points of `D.toBase`, additive for the relative group law attached to `hD`, equivariant for the action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ by composition with the induced morphism of spectra, and compatible with `ajbar`: for points $x, s$ with $s$ lying over `𝔛.εinf`, there is a degree-zero divisor equal to $[\,\text{place of }x\,] - [\,\text{place of }s\,]$ whose class is sent by `pts` to $x$ followed by `ajbar`.
--
--   *Level $\Gamma_N$ side* : a valuation subring $A$ of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p` (that is, $p$ is a non-unit of $A$), residue field of characteristic $p$ and algebraically closed, a ring homomorphism $\rho : R_p \to A$ lifting the structure map to $\overline{\mathbb{Q}}$ (`hρ`); a designation $D_0$ of the relative $\mathrm{Pic}^0$ for `toBase p (ΓN p M H hpM) hj` with `hD₀` asserting that it represents the corresponding rigidified functor for the section `𝔛.εinf` followed by `𝔛.π`.
--
--   *Degeneracy embeddings of function fields* (`αH`, `βH`, `hαint`, `hβint`, `Meta₀`, `eeta₀`, `heeta₀`, `hMeta₀π`, `hMeta₀πw`, `degPts`, `hdeg0`, `hdeg1`): two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha_H, \beta_H$ from `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` into $\bar F_{M,H}$; a curve model `Meta₀` for the smaller field together with an isomorphism `eeta₀` onto the base change of `toBase p (ΓN p M H hpM) hj` to $\overline{\mathbb{Q}}$ compatible with the structure morphisms; the two pins saying that points of `Meta₀.C` lying under a point of `𝔛.Meta.C` via `𝔛.π` (respectively via `𝔛.w` followed by `𝔛.π`) have place the restriction along $\alpha_H$ (respectively $\beta_H$) of the place of that point; and two additive maps `degPts 0`, `degPts 1` from $J_H(M)$ to $J_H(M/p)$ pinned by the requirement that they send the class of a degree-zero divisor $D_v$ to the class of its push-forward along $\alpha_H$, respectively $\beta_H$.
--
--   *Generic Abel–Jacobi and points block at level $\Gamma_N$* (`hDQ₀`, `hPQ₀`, `ajQ₀`, `hajQ₀ε`, `hajQ₀`, `kQ₀`, `hkQ₀₁`, `hkQ₀₂`, `ajbar₀`, `hajbar₀`, `hajbar₀_over`, `εbar₀`, `hεbar₀`, `hεbar₀_aj`, `pts₀`, `hpts₀_add`, `hpts₀_aj`): the exact analogues of the level-$\Gamma_M$ blocks above for $D_0$, `Meta₀` and the section `𝔛.εinf` followed by `𝔛.π`, ending with a bijection `pts₀` from $J_H(M/p)$ to the $\overline{\mathbb{Q}}$-points of `D₀.toBase`, additive for the relative group law of `hD₀` and compatible with `ajbar₀` in the same divisorial sense.
--
--   *Special fibre at level $\Gamma_N$* (`ptsSp₀`, `hptsSp₀_add`, `hptsSp₀`): a bijection `ptsSp₀` from $\mathrm{Pic}^0$ of the residue field of $A$ with the function field `Fbar p M H hpM (ResidueField A)` onto the points of `D₀.toBase` over `resPt A` followed by $\operatorname{Spec} \rho$, additive for the base-changed relative group law of `hD₀`, and a clause (nine data and hypotheses, summarised here) pinning `ptsSp₀` against the Abel–Jacobi map of the special fibre: given two $A$-points $v_1, v_2$ of the level-$\Gamma_N$ curve with their reductions $v_{\kappa,1}, v_{\kappa,2}$ into the fibre, closed points $Q_1, Q_2$ of `𝔛.Mfib` reducing to them, and a degree-zero divisor $D_w$ equal to the difference of the places of $Q_1$ and $Q_2$, there is an $A$-point $s_0$ of `D₀.toBase` classifying $\mathcal{O}(v_1) \otimes I_{v_2}$ whose restriction to the residue field corresponds under `ptsSp₀` to the class of $D_w$.
--
--   *Special fibre at level $\Gamma_M$, glued dictionary* (`SS`, `t`, `ptsSp`, `abq`, `τ`, `B`, `hS`): a finite set `SS` of pairs of places of `Fbar p M H hpM (ResidueField A)`, a natural number $t$, a bijection `ptsSp` from the glued $\mathrm{Pic}^0$ of `SS` (admissible triples consisting of two degree-zero divisors vanishing on the first, respectively second, coordinates of the pairs in `SS` together with a family of units indexed by `SS`, modulo glued principal data) onto the points of `D.toBase` over the special point, two morphisms `abq 0`, `abq 1` between the special fibres of `D` and $D_0$, a morphism $\tau$ from the split torus of rank $t$ over the residue field into the special fibre of $D$, and an isomorphism $B$ from the character lattice of `SS` (the degree-zero part of $\mathbb{Z}^{SS}$) onto $\mathbb{Z}^t$. The hypothesis `hS` (twelve clauses, summarised here) requires: `SS` is exactly the set `ssNodePairsQExp` of supersingular node pairs attached to $p$ at level `ΓN p M H hpM`; $t + 1$ is the cardinality of `SS`; `ptsSp` is additive for the base-changed relative group law of `hD`; an Abel–Jacobi pin for `ptsSp` in the glued setting, for each $i \in \{0,1\}$, matching two $A$-points of the level-$\Gamma_M$ curve with image in the smooth locus, their reductions, closed points $P_1, P_2$ of `𝔛.Mfib` above them via `𝔛.efib` followed by `𝔛.comp … i`, and an admissible glued datum whose $i$-th divisor component is the difference of the places of $P_1$ and $P_2$, the other divisor component and the unit component being zero; the `abq i` are homomorphisms for the base-changed group laws; the morphism to the fibre product induced by `abq 0` and `abq 1` is flat and surjective; its kernel is exactly the image of $\tau$, in the sense that a point of the special fibre of $D$ is killed by both `abq i` precisely when it factors through $\tau$; the `abq i` commute with automorphisms of the base point; `ptsSp₀` transports `abq i` applied to `ptsSp x` to the first, respectively second, component of `GluedPic0.toPic0Pair SS x`; $\tau$ is a closed immersion; $\tau$ is multiplicative on torus points; a point of the glued $\mathrm{Pic}^0$ lies in the image of $\tau$ exactly when it lies in the range of `GluedPic0.nodeUnit SS`; and, finally, a torus point $\chi$ corresponds under $\tau$ to `ptsSp (GluedPic0.nodeUnit SS w)` precisely when for every $a$ in the character lattice the product $\prod_s w(s)^{a(s)}$ equals $\chi$ evaluated at the monomial $B(a)$.
--
--   Under these hypotheses there exists a family `degHom : Fin 2 → SchemeHomOver D.toBase D₀.toBase`, that is two morphisms $D \to D_0$ over $\operatorname{Spec} R_p$, with the following three properties.
--
--   First, each `degHom i` is a homomorphism: for every $i$, every scheme $T$ with a morphism $s$ to `base p` and all points $x, y$ of `D.toBase` over $s$, composing the product of $x$ and $y$ for the relative group law attached to `hD` with `degHom i` equals the product, for the relative group law attached to `hD₀`, of $x$ composed with `degHom i` and $y$ composed with `degHom i`.
--
--   Second, on $\overline{\mathbb{Q}}$-points the `degHom i` realise the divisor push-forwards: for every $i$ and every $x \in J_H(M)$, the point `pts₀ (degPts i x)` equals `pts x` followed by `degHom i`.
--
--   Third, a formula on the special fibre: for every unit $\bar e$ of $\mathbb{Z}/(M/p)$ with $\bar e \cdot p = 1$ in $\mathbb{Z}/(M/p)$ and every point $x$ of `D.toBase` over the special point `resPt A` followed by $\operatorname{Spec} \rho$,
--   $$\mathrm{ptsSp_0}^{-1}(x \circ \mathrm{degHom}\,0) = \mathrm{ptsSp_0}^{-1}(\mathrm{abq}\,0\,(x)) + F\bigl(\mathrm{ptsSp_0}^{-1}(\mathrm{abq}\,1\,(x))\bigr),$$
--   $$\mathrm{ptsSp_0}^{-1}(x \circ \mathrm{degHom}\,1) = F\bigl(\mathrm{ptsSp_0}^{-1}(\mathrm{abq}\,0\,(x))\bigr) + \langle \bar e \rangle \cdot \mathrm{ptsSp_0}^{-1}(\mathrm{abq}\,1\,(x)),$$
--   where $F$ is `qExpFrobeniusPushforwardModL (ResidueField A) (ΓN p M H hpM) p`, the diamond operator acts through `SemilinearAut.ofAlgAut` applied to `diamondActionModL (ResidueField A) (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) ē)`, and `abq i (x)` denotes `fibreMap (abq i) x`.
--
--   This is the construction of the two degeneracy maps $\pi_*$ and $(\pi w)_*$ as homomorphisms between the relative $\mathrm{Pic}^0$ objects of the Deligne–Rapoport models of $X_H(M)$ and $X_H(M/p)$ over $\mathbb{Z}_{(p)}$, pinned on $\overline{\mathbb{Q}}$-points by divisor push-forward and, on the special fibre at $p$, by Ribet's formula expressing them through the abelian-quotient coordinates, the geometric Frobenius push-forward and a diamond operator. It is used in assembling the level data and dictionary of the Néron object of $J_H(M)$ at $p$, which in turn feeds the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_degeneracyHom_mul_pts_special.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

set_option maxHeartbeats 800000 in

theorem ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    [IsProper (toBase p (ΓN p M H hpM) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hMeta₀π : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y))
    (hMeta₀πw : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y))
    (degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM)))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)

    (hDQ₀ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))) (D₀.baseChange ℚ))
    (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) ℚ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ₀ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (D₀.baseChange ℚ).toBase)
    (hajQ₀ε : (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1 ≫ ajQ₀.1 = (D₀.baseChange ℚ).zeroSection)
    (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)),
      Nonempty ((hDQ₀.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (t ≫ (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ₀ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ))
    (hkQ₀₁ : kQ₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p))
    (hkQ₀₂ : kQ₀ ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar₀ : Meta₀.C ⟶ D₀.P) (hajbar₀ : ajbar₀ = eeta₀ ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst D₀.toBase (specMap (R p) ℚ))
    (hajbar₀_over : ajbar₀ ≫ D₀.toBase = Meta₀.toBase ≫ genPt p)
    (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
    (hεbar₀ : εbar₀.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1)
    (hεbar₀_aj : εbar₀.1 ≫ ajbar₀ = genPt p ≫ D₀.zeroSection)

    (pts₀ : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) D₀.toBase)
    (hpts₀_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM),
      pts₀ (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (pts₀ x) (pts₀ y))
    (hpts₀_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
        (pts₀ (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀)
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

    [IsSeparated (toBase p (ΓM M H) hj)]
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
        Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (t : ℕ)
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (abq : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase))
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase))
    (B : characterLattice ↥SS ≃+ (Fin t → ℤ))
    (hS :
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
              χ (AddMonoidAlgebra.single (B a) 1)))
    :
    ∃ degHom : Fin 2 → SchemeHomOver D.toBase D₀.toBase,

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) (degHom i) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul s
            (NeronModelInfra.schemeHomOverComp x (degHom i)) (NeronModelInfra.schemeHomOverComp y (degHom i))) ∧

      (∀ (i : Fin 2) (x : JH M H), (pts₀ (degPts i x)).1 = (pts x).1 ≫ (degHom i).1) ∧

      (∀ (ē : (ZMod (M / p))ˣ), ((ē : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
        ∀ x : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase,
          ptsSp₀.symm (NeronModelInfra.schemeHomOverComp x (degHom 0)) =
              ptsSp₀.symm (fibreMap (abq 0) x) +
                qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (ptsSp₀.symm (fibreMap (abq 1) x)) ∧
          ptsSp₀.symm (NeronModelInfra.schemeHomOverComp x (degHom 1)) =
              qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (ptsSp₀.symm (fibreMap (abq 0) x)) +
                SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) ē)) •
                  ptsSp₀.symm (fibreMap (abq 1) x)) := by sorry

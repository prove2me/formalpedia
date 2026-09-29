-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_pullback_baseChangeSnd_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul
-- name    : ModularCurve.XHDRModelAtP.nonempty_pullback_baseChangeSnd_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/ef9b1657-e62b-5ff2-b5bc-bbb8bd36a4bc
-- title:
--   Crossing-chart glued module restricts to 𝒪(̄ y₁)⊗𝒪(̄ y₂)⁻¹ generically
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field of $\mathrm{SL}(2,\mathbb{Z})$, and a model datum $\mathfrak{X}$ of type `XHDRModelAtP p M H hpM hj` with `toBase p (ΓM M H) hj` proper. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, let $\rho : R p \to A$ be a ring homomorphism compatible with the structure map $R p \to \overline{\mathbb{Q}}$, and let $\psi$ be a morphism over `genPt p` along `Spec.map ρ` whose underlying morphism is `barPt A`. Let $\bar y_1,\bar y_2$ be $\overline{\mathbb{Q}}$-points of $X$ over `genPt p`. Write $X$ for the base change $\mathrm{pullback}$ of `toBase` along `Spec.map ρ`, $Q = A[U,V]/(UV - p^e)$ for some $e \ge 1$, and $\mathrm{Mdl} = \operatorname{Spec} Q$. Assume given an open $U \subseteq X$ and an $A$-morphism $f : U \to \mathrm{Mdl}$ (i.e. $f$ followed by $\operatorname{Spec}$ of $A \to Q$ equals $U \hookrightarrow X$ followed by the second projection), an open $W_{\mathrm{et}} \subseteq U$ on which the restriction of $f$ is étale, and two sections $s_U, s_U' : \operatorname{Spec} A \to U$ of $X \to \operatorname{Spec} A$ whose closed points lie in $W_{\mathrm{et}}$, such that the graph of $\bar y_2$ followed by `baseChangeSnd … ψ` is `barPt A` followed by $s_U$, and likewise the graph of $\bar y_1$ with $s_U'$. Assume $x', y'$ lie in the maximal ideal of $A$ with $x'y' = p^e$, $w \in A^\times$, that $f \circ s_U$ is $\operatorname{Spec}$ of the $A$-algebra map $Q \to A$ determined by $(x', y')$ and $f \circ s_U'$ that determined by $(wx', w^{-1}y')$, and that $s_U'$ is determined by $f \circ s_U'$ among these two sections ($f \circ s_U' = f \circ s_U \Rightarrow s_U' = s_U$). Put $a, b, a_w, b_w \in \Gamma(\mathrm{Mdl},\top)$ the global sections corresponding under the inverse of `Scheme.ΓSpecIso` to $U - x'$, $y' - V$, $U - wx'$ and $y' - wV$ in $Q$, where `CrossingQuotient.U` and `CrossingQuotient.V` are the distinguished elements of $Q$, and $O = (D(a)\cup D(b)) \cap (D(a_w)\cup D(b_w))$. The assertion is: for every $g \in \Gamma(\mathrm{Mdl}, D(a)\cup D(b))$ with $g\,a = a_w$ on $D(a)$, $g\,b = b_w$ on $D(b)$ and $g$ a unit on $O$; for all opens $W_2, W_3 \subseteq X$ with $W_2 \cup W_3 = \top$, $W_2 \subseteq U$, $W_2 \cap W_3$ contained in the image of $f^{-1}(O)$ under $U \hookrightarrow X$, and $W_3$ exactly the complement of the union of the images of $s_U$ and $s_U'$; with $t \in \Gamma(X, W_2 \cap W_3)$ the restriction of the section obtained by pulling $g|_O$ back along $f$ and transporting it to $X$ along the open immersion; for every module $L$ on $X$ and sections $a_L \in \Gamma(L,W_2)$, $b_L \in \Gamma(L,W_3)$ which are frames on $W_2$ and $W_3$ respectively (for every open $W$ inside the relevant one, multiplication by the restricted section is a bijection $\Gamma(X,W) \to \Gamma(L,W)$) and satisfy $b_L|_{W_2 \cap W_3} = t \cdot a_L|_{W_2 \cap W_3}$, the pullback of $L$ along `baseChangeSnd … ψ` is isomorphic to the tensor product of the dual of the ideal sheaf module of the graph of $\bar y_1$ with the ideal sheaf module of the graph of $\bar y_2$ on the geometric generic fibre; the conclusion is stated as nonemptiness of the set of such isomorphisms.
--
--   This is the generic-fibre half of the construction of the line bundle attached to a pair of $A$-sections meeting in a crossing chart $uv = p^e$ of the Deligne–Rapoport style model of $X_H$ at $p$: a module glued from frames on $W_2$ and on the complement of the two sections, with transition function the pullback of $(u-wx')/(u-x')$, becomes $\mathcal{O}(\bar y_1) \otimes \mathcal{O}(\bar y_2)^{-1}$ after restriction to the geometric generic fibre. It is used by [`ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter`](thm.html#ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter) in the analysis of the component group and inertia at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_nonempty_pullback_baseChangeSnd_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups
open MvPolynomial

set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.nonempty_pullback_baseChangeSnd_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ))) (hψ : ψ.1 = barPt A)
    (ybar₁ ybar₂ : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj))
    (e : ℕ) (he : 1 ≤ e)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) =
      U.ι ≫ pullback.snd _ _)

    (Wet : (U : Scheme.{0}).Opens) [AlgebraicGeometry.Etale (Wet.ι ≫ f)]

    (sU sU' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}))
    (hsU : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsU' : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)
    (hsW : sU.base (IsLocalRing.closedPoint ↥A) ∈ Wet) (hsW' : sU'.base (IsLocalRing.closedPoint ↥A) ∈ Wet)
    (hP₂ : graphOver (toBase p (ΓM M H) hj) ybar₂.1 ybar₂.2 ≫ baseChangeSnd (toBase p (ΓM M H) hj) ψ = barPt A ≫ sU ≫ U.ι)
    (hP₁ : graphOver (toBase p (ΓM M H) hj) ybar₁.1 ybar₁.2 ≫ baseChangeSnd (toBase p (ΓM M H) hj) ψ = barPt A ≫ sU' ≫ U.ι)

    (x' y' : ↥A) (hxy : x' * y' = ((p : ℕ) : ↥A) ^ e)
    (hx' : x' ∈ IsLocalRing.maximalIdeal ↥A) (hy' : y' ∈ IsLocalRing.maximalIdeal ↥A) (w : (↥A)ˣ)

    (hxyw : ((w : ↥A) * x') * ((↑w⁻¹ : ↥A) * y') = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
    (hxy₁ : x' * y' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
    (hfs : sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy₁).toRingHom))
    (hfs' : sU' ≫ f = Spec.map (CommRingCat.ofHom
      (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) ((w : ↥A) * x') ((↑w⁻¹ : ↥A) * y') hxyw).toRingHom))

    (huq : sU' ≫ f = sU ≫ f → sU' = sU) :
    letI X : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))
    letI Q := CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e)
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A Q x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥A Q y' - CrossingQuotient.V _)
    letI aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A Q ((w : ↥A) * x'))
    letI bw : Γ(Mdl, ⊤) := φ (algebraMap ↥A Q y' - algebraMap ↥A Q (w : ↥A) * CrossingQuotient.V _)
    letI O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)

    ∀ (gM : Γ(Mdl, Mdl.basicOpen a ⊔ Mdl.basicOpen b)),
      Mdl.presheaf.map (homOfLE (le_sup_left : Mdl.basicOpen a ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op a =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op aw →
      Mdl.presheaf.map (homOfLE (le_sup_right : Mdl.basicOpen b ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op b =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op bw →
      IsUnit (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM) →

    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    (∀ z, z ∈ W₃ ↔ (z ∉ Set.range (sU ≫ U.ι).base ∧ z ∉ Set.range (sU' ≫ U.ι).base)) →
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))

    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase p (ΓM M H) hj) ψ)).obj L ≅
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₁.1 ybar₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₂.1 ybar₂.2).idealModule) := by sorry

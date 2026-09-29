-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_torus_abq_specialFibre
-- name    : ModularCurve.XHDRModelAtP.exists_representsRelSubPic_torus_abq_specialFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/87004154-d4d4-5694-8a5e-476fdfc14713
-- title:
--   Torus and abelian quotient on the special fibre of Pic⁰
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field of full level over $\mathbb{Q}$. Let $\mathfrak{X}$ be a Deligne–Rapoport model datum in `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\rho : \mathtt{R}\,p \to A$ be a ring map compatible with the structure map $\mathtt{R}\,p \to \overline{\mathbb{Q}}$. Let $D$ (with `hD`) represent, over $\mathtt{R}\,p$, the functor of line bundles on the level-$\Gamma_M(M,H)$ curve `toBase p (ΓM M H) hj` rigidified along the section $\mathfrak{X}.\varepsilon_{\inf}$ and fibrewise algebraically trivial (the cut `algEquivZeroCut`), and let $\varepsilon_0$, $D_0$ (with `hD₀`) be the analogous section and representing designation for the level-$\Gamma_N(p,M,H)$ curve. Assume given a $\kappa$-point $\varepsilon_{0\kappa}$ of the fibre of the $\Gamma_N$-curve at $\mathrm{residue}\circ\rho$ which is the section induced by $\varepsilon_0$ (its composites with the two pullback projections are $\mathrm{Spec}(\mathrm{residue}\circ\rho)$ followed by $\varepsilon_0$, and the identity), and whose composite with the zeroth component map $(\mathfrak{X}.\mathrm{comp}\,A\,h_A\,\rho\,h_\rho)\,0$ of the special fibre is `sectionFibre 𝔛.εinf`. Regarding $\kappa$ as an $\mathtt{R}\,p$-algebra through $\mathrm{residue}\circ\rho$, the conclusion asserts: the number of points of the fibre product of the two component maps $(\mathfrak{X}.\mathrm{comp})\,0$ and $(\mathfrak{X}.\mathrm{comp})\,1$ equals the cardinality $s$ of `ssPlacesQExp κ (ΓN p M H hpM) p` (the places of the $q$-expansion function field of level $\Gamma_N$ over $\kappa$ satisfying `IsSSPlaceQExp` at $p$), and $s > 0$; and there exist representability data $h_{D\kappa}$, $h_{D_0\kappa}$ for the base changes to $\kappa$ of the two curves, with their sections base-changed, whose Poincaré bundles are isomorphic to the base changes along `BaseChange.ofR` of the Poincaré bundles of `hD`, `hD₀` pulled back along the first projection; a proof $h_{\varepsilon_1}'$ that the base-changed $\varepsilon_0$ followed by $(\mathfrak{X}.\mathrm{comp})\,0$ is the base-changed $\mathfrak{X}.\varepsilon_{\inf}$; a $\kappa$-morphism $\tau$ from the split torus `torusStr κ (s-1)` to $(D \otimes \kappa).\mathrm{toBase}$; and two morphisms $\mathrm{abq}\,0, \mathrm{abq}\,1$ from $(D \otimes \kappa).\mathrm{toBase}$ to $(D_0 \otimes \kappa).\mathrm{toBase}$ over $\kappa$, such that $\mathrm{abq}\,0$ is the pullback homomorphism `RepresentsRelSubPic.pullbackHom` along the zeroth component map; $\mathrm{abq}\,1$ is characterised on points by the property that for every scheme $T$ over $\kappa$ and every $T$-point $a$ of $(D \otimes \kappa).\mathrm{toBase}$ the Poincaré bundle of $h_{D_0\kappa}$ pulled back along $a$ followed by $\mathrm{abq}\,1$ is isomorphic to the rigidification along the base-changed $\varepsilon_0$ of the pullback, along `curveChange` of the first component map, of the Poincaré bundle of $h_{D\kappa}$ pulled back along $a$; $\tau$ is a closed immersion and is multiplicative, namely for characters $\chi, \chi'$ in `WithConv` of the $\kappa$-algebra maps `torusCoord κ (s-1) → κ` the torus point attached to $(\chi\chi').\mathrm{ofConv}$ composed with $\tau$ is the product, under the base change to $\kappa$ of the relative group law attached to `hD`, of the points attached to $\chi$ and $\chi'$; each $\mathrm{abq}\,i$ is a homomorphism for the base-changed relative group laws of `hD` and `hD₀`; the induced morphism to the fibre product of $\mathrm{abq}\,0$ and $\mathrm{abq}\,1$ is flat and surjective; and for every $T$-point $a$ of $(D \otimes \kappa).\mathrm{toBase}$, both composites $a \circ \mathrm{abq}\,i$ are the identity section of the group law of `hD₀` over $\kappa$ if and only if $a$ factors as $y$ followed by $\tau$ for some $T$-point $y$ of the split torus.
--
--   This is the structure of the relative $\mathrm{Pic}^0$ of the special fibre at a place above $p$ of the Deligne–Rapoport model of the modular curve of level $\Gamma_H(M)$ with $p \parallel M$: the fibre is an extension of two copies of the $\mathrm{Pic}^0$ of the smooth level-$\Gamma_N$ curve by a split torus of rank one less than the number of supersingular places, the torus being the kernel of the pair of restriction maps to the two components. It is used in the description of the points of the special fibre of the associated Néron object and in the analysis of multiplication-by-$n$ on that fibre, the input for the Néron-model and component-group arguments behind level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_torus_abq_specialFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.SplitTorus
  ModularCurve ModularCurve.XHDRLevel IsLocalRing
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_representsRelSubPic_torus_abq_specialFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (ρ : XHDRLevel.R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))

    (D : RelativePic0Designation (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj))
    (hD : RepresentsRelSubPic (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj) 𝔛.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (XHDRLevel.R p)))) (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj))
    (D₀ : RelativePic0Designation (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) ε₀ (algEquivZeroCut (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) ε₀) D₀)

    (ε₀κ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ XHDRLevel.fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((residue ↥A).comp ρ))
    (hε₀κ₁ : ε₀κ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)) ≫ ε₀.1) (hε₀κ₂ : ε₀κ ≫ pullback.snd _ _ = 𝟙 _)
    (hε₁ : ε₀κ ≫ (𝔛.comp A hA ρ hρ) 0 = sectionFibre 𝔛.εinf ((residue ↥A).comp ρ)) :
    letI : Algebra (XHDRLevel.R p) (ResidueField ↥A) := ((residue ↥A).comp ρ).toAlgebra

    Nat.card ↥(pullback ((𝔛.comp A hA ρ hρ) 0) ((𝔛.comp A hA ρ hρ) 1)) =
        Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) ∧
    0 < Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) ∧

    ∃ (hDκ : RepresentsRelSubPic (baseChange (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔛.εinf)
        (algEquivZeroCut (baseChange (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔛.εinf)) (D.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj) 𝔛.εinf (ResidueField ↥A)
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (XHDRLevel.R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hD₀κ : RepresentsRelSubPic (baseChange (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) ε₀)
        (algEquivZeroCut (baseChange (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) ε₀)) (D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) ε₀ (ResidueField ↥A)
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (XHDRLevel.R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hε₁' : (sectionBaseChange (ResidueField ↥A) ε₀).1 ≫ (𝔛.comp A hA ρ hρ) 0 = (sectionBaseChange (ResidueField ↥A) 𝔛.εinf).1)
      (τ : SchemeHomOver (torusStr (ResidueField ↥A) (Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) - 1)) (D.baseChange (ResidueField ↥A)).toBase)
      (abq : Fin 2 → SchemeHomOver (D.baseChange (ResidueField ↥A)).toBase (D₀.baseChange (ResidueField ↥A)).toBase),

      abq 0 = RepresentsRelSubPic.pullbackHom ((𝔛.comp A hA ρ hρ) 0) ((𝔛.comp_over A hA ρ hρ) 0)
        hε₁' hDκ hD₀κ ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) (ResidueField ↥A)) t (sectionBaseChange (ResidueField ↥A) ε₀))
              (pullback.snd (baseChange (XHDRLevel.R p) (XHDRLevel.toBase p (XHDRLevel.ΓN p M H hpM) hj) (ResidueField ↥A)) t)
            ((Scheme.Modules.pullback (curveChange ((𝔛.comp A hA ρ hρ) 1)
              ((𝔛.comp_over A hA ρ hρ) 1) t)).obj (hDκ.poincare.pullbackAlong a).L))) ∧

      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) (Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) - 1) →ₐ[ResidueField ↥A] (ResidueField ↥A)),
        NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField ↥A) (Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) - 1) (χ * χ').ofConv) τ =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (specMap (XHDRLevel.R p) (ResidueField ↥A))).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField ↥A) (Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId (ResidueField ↥A) (Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) - 1) χ'.ofConv) τ)) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a b : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
        NeronModelInfra.schemeHomOverComp
            (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (specMap (XHDRLevel.R p) (ResidueField ↥A))).mul t a b)
            (abq i) =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (XHDRLevel.R p) (ResidueField ↥A))).mul t
            (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i))) ∧

      Flat (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧
      Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
        (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (XHDRLevel.R p) (ResidueField ↥A))).one t) ↔
          ∃ y : SchemeHomOver t (torusStr (ResidueField ↥A) (Nat.card ↥(ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) - 1)),
            NeronModelInfra.schemeHomOverComp y τ = a) := by sorry

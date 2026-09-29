-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/070ecd8f-5d4e-58d5-899c-7c8fa4e0bbc6
-- title:
--   Diamond translate of a configured point on the Deligne–Rapoport model
-- statement:
--   Fix a prime $p$, a nonzero level $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field of level $\mathrm{SL}(2,\mathbb{Z})$, and a bundle $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj`. Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and a ring map $\rho : R(p) \to A$ compatible with $\overline{\mathbb{Q}}$ (i.e. $A \hookrightarrow \overline{\mathbb{Q}}$ precomposed with $\rho$ is the structure map). Assume `hdia0`: for each $e \in (\mathbb{Z}/(M/p))^\times$ and each closed point $P$ of the curve model `𝔛.Mfib A hA ρ hρ`, transporting $P$ through `𝔛.efib`, the map on fibres over `residue ∘ ρ` induced by the automorphism `𝔛.dia0 e` (which lies over `toBase`), and the inverse of `𝔛.efib` again gives a closed point, whose place is the place of $P$ translated by the semilinear automorphism $(\sigma,1)$ with $\sigma =$ `diamondActionModL (ResidueField A) (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) e)`, where `infSubgroup` is the image of $H$ under `ZMod.unitsMap`. Fix $d \in (\mathbb{Z}/M)^\times$ and $i : \mathrm{Fin}\,2$, and a configured datum: a section $y$ of `𝔛.Meta.toBase` over $\overline{\mathbb{Q}}$; a morphism $u : \operatorname{Spec} A \to X(p,\Gamma_M(M,H),hj)$ over `Spec.map ρ`, whose base change along $A \hookrightarrow \overline{\mathbb{Q}}$ is $y$ followed by `𝔛.eeta` and the first projection, and whose topological image lies in `𝔛.smoothLocus`; a section $u_\kappa$ of the second projection of the fibre over `residue ∘ ρ` whose first projection is the reduction of $u$; and a closed point $P$ of `𝔛.Mfib A hA ρ hρ` with $(\mathfrak{X}.\mathrm{efib} \ \text{followed by}\ \mathfrak{X}.\mathrm{comp}\,i)$ sending $P$ to the image of the closed point under $u_\kappa$. The conclusion asserts the existence of $y'$ and $u'$ with the same three properties (generic fibre $y'$, image in the smooth locus), with $u'$ equal to $u$ followed by the automorphism `(𝔛.dia d).hom`, with `𝔛.Meta.pointEquivPlace y'` equal to `SemilinearAut.ofAlgAut (diamondAutHBar M H d)` applied to `𝔛.Meta.pointEquivPlace y`, and with a section $u'_\kappa$ of the second projection reducing $u'$, equal to $u_\kappa$ followed by the fibre map induced by `𝔛.dia d`, together with a closed point $P'$ of `𝔛.Mfib A hA ρ hρ` lying over the closed point of $u'_\kappa$ through the same $i$-th composite, whose place is the place of $P$ translated by the semilinear automorphism attached to `diamondActionModL (ResidueField A) (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))`.
--
--   This is the diamond-operator equivariance of a point configuration on the Deligne–Rapoport type model of $X_H(M)$ over $\mathbb{Z}_{(p)}$: applying $\langle d \rangle$ moves the generic place by the diamond automorphism of the geometric function field and the place on the $i$-th component of the special fibre by the characteristic-$p$ diamond attached to the reduction $\bar d$ modulo $M/p$, while keeping the section inside the smooth locus and on the same component. It is used by [`ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap`](thm.html#ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap) and by [`ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum), where the diamond action on points of the special fibre is compared with the action on the character group of the toric part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_comp_dia_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((XHDRLevel.fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)
    (d : (ZMod M)ˣ) (i : Fin 2)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    ∃ (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      u'.1 = u.1 ≫ (𝔛.dia d).hom ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ' = uκ ≫ XHDRLevel.fibreMap (Γ := ΓM M H) (Γ' := ΓM M H) (overOfIso (𝔛.dia d) (𝔛.dia_over d))
          ((IsLocalRing.residue ↥A).comp ρ) ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          (𝔛.Mfib A hA ρ hρ).placeOfPoint P' =
            SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_comp_one_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
-- name    : ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_comp_one_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/64840a18-b27c-5104-8fc3-0fce2e47e60a
-- title:
--   Order at non-supersingular points of the Atkin–Lehner fibre component
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction to $(\mathbb{Z}/(M/p))^\times$ is $1$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$ and with algebraically closed residue field of characteristic $p$, let `jqModC ℚ` lie in the $q$-expansion function field of full level, and let $\mathfrak{X}$ be a term of [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81), with $\rho : R p \to Pl$ a lift of the structure map $R p \to \overline{\mathbb{Q}}$ along the inclusion of $Pl$. Assume given an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $\overline{\mathbb{Q}}\cdot F_H(M)$ = `xHFunctionFieldBar M H` which implements the involution $\mathfrak{X}.w$ on places: whenever two $\overline{\mathbb{Q}}$-sections $y,y'$ of $\mathfrak{X}.\mathtt{Meta}$ satisfy that $y'$ followed by `eeta`, the first pullback projection and $\mathfrak{X}.w.\mathrm{hom}$ agrees with $y$ followed by `eeta` and that projection, then the place attached to $y'$ is the image of the place attached to $y$ under the semilinear automorphism `SemilinearAut.ofAlgAut θ`. Let $f \in \overline{\mathbb{Q}}\cdot F_H(M)$, let $x,y$ be Laurent series over $Pl$ whose coefficientwise residues are nonzero, suppose $\theta f$, viewed as a Laurent series over $\overline{\mathbb{Q}}$, satisfies $(\theta f)\cdot y = x$ after mapping $x,y$ into $\overline{\mathbb{Q}}$, and let $g$ in the $q$-expansion function field of level `ΓN p M H hpM` over the residue field $\kappa$ of $Pl$ satisfy $g \cdot \bar y = \bar x$ for the coefficientwise residues. Let $\iota$ be a finite index type, $yv_j$ sections of $\mathfrak{X}.\mathtt{Meta}.\mathtt{toBase}$, $u_j$ points of the integral model $X p (\Gamma_M(H))$ over $\mathrm{Spec}\,\rho$ whose $\overline{\mathbb{Q}}$-specialisations are the $yv_j$, $u\kappa_j$ sections of the fibre over $\kappa$ reducing $u_j$ (first projection $=$ the $\kappa$-reduction of $u_j$, second projection the identity), and $n_j \in \mathbb{Z}$ with $\mathrm{ord}_v f = \sum_j n_j$ over those $j$ with place $(yv_j) = v$, for every place $v$ of $\overline{\mathbb{Q}}\cdot F_H(M)$. Then for every closed point $\bar P$ of the curve $(\mathfrak{X}.\mathtt{Mfib}\,Pl\,h_{Pl}\,\rho\,h_\rho).C$ whose associated place does not lie in [`ModularCurve.ssPlacesQExp κ (ΓN p M H hpM) p`](def/ModularCurve_XHDifferentialsModL.html#L27), the order of $g$ at that place equals $\sum_j n_j$, the sum taken over those $j$ for which the image of $\bar P$ under $\mathfrak{X}.\mathtt{efib}$ followed by the component map $\mathfrak{X}.\mathtt{comp}\,1$ coincides with the image of the closed point of $\mathrm{Spec}\,\kappa$ under $u\kappa_j$.
--
--   This is the horizontal divisor specialisation law on the component indexed $1$ of the geometric special fibre of the Deligne–Rapoport model of $X_H(M)$ at $p$: at a closed point of that component which is not supersingular, the order of the reduced function counts, with multiplicities $n_j$, the divisor points of $f$ whose integral sections specialise to that point. It is the transport along the Atkin–Lehner involution $\mathfrak{X}.w$, through the automorphism $\theta$ of the geometric function field, of [`ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap`](thm.html#ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap), which is the corresponding law on the other component; it feeds the local semicontinuity statement [`ModularCurve.XHDRModelAtP.localSemicontinuity_prolongationDatum_offDiag`](thm.html#ModularCurve.XHDRModelAtP.localSemicontinuity_prolongationDatum_offDiag) and the regularity statement for integral functions at affine places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_comp_one_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 800000 in
open Classical in
open ModularCurve in

theorem ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_comp_one_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (f : ↥(ModularCurve.xHFunctionFieldBar M H))
    (x y : LaurentSeries ↥Pl)
    (hxbar : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x ≠ 0)
    (hybar : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)
    (hfxy : ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y =
      ModularCurve.coeffMap Pl.subtype x)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    (hg : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    {ι : Type} [Fintype ι]
    (yv : ι → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : ι → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : ∀ j, barPt Pl ≫ (u j).1 = (yv j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : ι → (Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
    (huκ₁ : ∀ j, uκ j ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u j).1)
    (huκ₂ : ∀ j, uκ j ≫ pullback.snd _ _ = 𝟙 _)
    (n : ι → ℤ)
    (hdiv : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      v.ord f = (∑ j, Finsupp.single (𝔛.Meta.pointEquivPlace (yv j)) (n j)) v)

    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (hPbar : (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar ∉
      ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM) p) :
    ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord g =
      ∑ j, if (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 1).base Pbar.1 =
              (uκ j).base (IsLocalRing.closedPoint (ResidueField ↥Pl))
           then n j else 0 := by sorry

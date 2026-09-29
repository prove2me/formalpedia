-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
-- name    : ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/2b099f1f-2471-5e66-855b-747628e3d436
-- title:
--   Gauss witness for a section and its reduction at ∞
-- statement:
--   Fix a prime $p$, an $M \ge 1$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under $\mathrm{ZMod.unitsMap}$ for $M/p \mid M$ is $1$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$, whose residue field has characteristic $p$ and is algebraically closed, and let $hj$ record that $\mathrm{jqModC}\ \mathbb{Q}$ lies in $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ \top$. Let $\mathfrak{X}$ be a term of [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81), and $\rho : R\,p \to Pl$ a ring homomorphism whose composite with the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R\,p \to \overline{\mathbb{Q}}$. Let $\mathcal{X} = \mathrm{X}\,p\,(\Gamma_M(M,H))\,hj \times_{\operatorname{Spec} R\,p} \operatorname{Spec} Pl$. Assume given $gA : \mathfrak{X}.\mathrm{Meta}.C \to \mathcal{X}$ with $gA$ followed by the first projection equal to $\mathfrak{X}.\mathrm{eeta}$ followed by the first projection, and $gA$ followed by the second projection equal to $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by $\mathrm{barPt}\ Pl$; and a morphism $bc$ from the fibre of $\mathrm{toBase}\ p\ (\Gamma_M(M,H))\ hj$ along $\operatorname{Spec}$ of the residue map composed with $\rho$ into $\mathcal{X}$, commuting with the first projections and satisfying that $bc$ followed by the second projection equals the second projection followed by $\operatorname{Spec}$ of the residue map. Let $\bar P$ be a closed point of the curve $(\mathfrak{X}.\mathrm{Mfib}\ Pl\ hPl\ \rho\ h\rho).C$, let $U$ be an open of $\mathcal{X}$ containing the image of $\bar P$ under $\mathfrak{X}.\mathrm{efib}$ followed by the $0$-th component map $\mathfrak{X}.\mathrm{comp}\ \cdots\ 0$ and then $bc$, assume $gA^{-1}U$ nonempty, and let $s \in \Gamma(\mathcal{X}, U)$. Then $(\mathfrak{X}.\mathrm{efib} \cdots \gg bc)^{-1}U$ is nonempty and there are Laurent series $x_s, y_s$ with coefficients in $Pl$ such that the coefficientwise residue of $y_s$ is nonzero; the element of $\mathrm{xHFunctionFieldBar}\ M\ H$ obtained from the germ in the function field of $\mathfrak{X}.\mathrm{Meta}.C$ of $(gA.\mathrm{app}\ U)\,s$ via $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$, viewed as a Laurent series over $\overline{\mathbb{Q}}$, times the image of $y_s$ under $Pl \hookrightarrow \overline{\mathbb{Q}}$ equals the corresponding image of $x_s$; the element of $\mathrm{qExpFunctionFieldC}$ of the residue field at level $\Gamma_N(p,M,H)$ obtained in the same way from the germ of the pullback of $s$ along $\mathfrak{X}.\mathrm{efib} \gg \mathfrak{X}.\mathrm{comp}\cdots 0 \gg bc$, viewed as a Laurent series over the residue field, times the coefficientwise residue of $y_s$ equals the coefficientwise residue of $x_s$; and if $s$ is a unit then this last function has order $0$ at the place $(\mathfrak{X}.\mathrm{Mfib}\cdots).\mathrm{placeOfPoint}\ \bar P$.
--
--   This is a $q$-expansion comparison in the style of the Katz $q$-expansion principle for the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: the germ of a section near a point of the special-fibre component through the cusp $\infty$ is exhibited as a ratio $x_s/y_s$ of Laurent series with coefficients in the valuation ring, whose generic reading is the function on the geometric generic fibre and whose coefficientwise reduction is the function on that component, with no pole or zero at the chosen closed point when $s$ is invertible. It feeds the computations of orders of vanishing on the special fibre used in the Néron-model and level-lowering arguments, and is cited by the statements about crossing points and about divisibility of orders for the Jacobian at level $H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.lean

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

theorem ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hzU : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
    (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
    (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U)))
      (xs ys : LaurentSeries ↥Pl),

      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys ≠ 0 ∧
      (((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.coeffMap Pl.subtype ys = ModularCurve.coeffMap Pl.subtype xs ∧

      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys =
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xs ∧

      (IsUnit s → ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord
        ((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) = 0) := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_zero_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq
-- name    : ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_zero_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/1b2e3df1-b764-589b-9268-fa3c4378c22a
-- title:
--   Unit sections have reduction of order zero at ̄ P
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial, and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$, whose residue field has characteristic $p$ and is algebraically closed; assume $j$ lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$ over $\mathbb{Q}$, and let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` together with a ring homomorphism $\rho : R p \to Pl$ compatible with $\overline{\mathbb{Q}}$, i.e. $Pl.\mathrm{subtype} \circ \rho = \mathrm{algebraMap}$. Let $f$ belong to the base change of the function field of $X_H(M)$ to $\overline{\mathbb{Q}}$, let $x, y$ be Laurent series over $Pl$ whose coefficientwise reductions to the residue field are non-zero, with $f \cdot y = x$ after coefficientwise inclusion into $\overline{\mathbb{Q}}$, and let $g$ lie in the $q$-expansion function field over the residue field for $\Gamma_N(p,M,H)$, with $g \cdot \bar y = \bar x$ coefficientwise. Let $gA$ be a morphism from $\mathfrak{X}.\mathrm{Meta}.C$ to the pullback of `toBase p (ΓM M H) hj` along $\mathrm{Spec}\,\rho$ whose first projection agrees with that of $\mathfrak{X}.\mathrm{eeta}$ and whose second projection is $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by `barPt Pl`, and let $bc$ be a morphism from the fibre over $\mathrm{residue} \circ \rho$ to the same pullback commuting with the first projection and compatible with the second via $\mathrm{Spec}$ of the residue map. Let $\bar P$ be a closed point of the curve of $\mathfrak{X}.\mathrm{Mfib}\ Pl\ hPl\ \rho\ h\rho$, and suppose there are an open $U$ of the pullback containing the image of $\bar P$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\ \cdots\ 0$ and then $bc$, with $gA^{-1}U$ non-empty, and a unit section $s \in \Gamma(U)$ whose germ at the function field of $\mathfrak{X}.\mathrm{Meta}.C$, pulled back along $gA$ and transported by $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$, equals $f$. Then the order of $g$ at the place `placeOfPoint` $\bar P$ of the curve model $\mathfrak{X}.\mathrm{Mfib}\ Pl\ hPl\ \rho\ h\rho$ is $0$.
--
--   This is the step asserting that a function on the Deligne–Rapoport model which is a unit of the local ring at a point of the special fibre has reduction of valuation zero at the corresponding place of the reduced curve; the order in question is that attached to the place by the divisor-theoretic `ord` of a `Place`. It feeds the construction of configured Galois representations in [`ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero`](thm.html#ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_zero_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq.lean

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

theorem ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_zero_of_isUnit_of_ffEquiv_symm_germToFunctionField_eq

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (f : ↥(ModularCurve.xHFunctionFieldBar M H))
    (x y : LaurentSeries ↥Pl)
    (hxbar : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x ≠ 0)
    (hybar : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)
    (hfxy : (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    (hg : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)

    (hunit : ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (_ : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
        (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
        IsUnit s ∧
        𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) = f) :
    ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord g = 0 := by sorry

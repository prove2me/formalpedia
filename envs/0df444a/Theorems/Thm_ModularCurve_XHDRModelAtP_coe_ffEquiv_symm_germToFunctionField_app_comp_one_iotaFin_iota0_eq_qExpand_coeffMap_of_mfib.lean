-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_one_iotaFin_iota0_eq_qExpand_coeffMap_of_mfib
-- name    : ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_one_iotaFin_iota0_eq_qExpand_coeffMap_of_mfib
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/0735bcc5-c765-5b30-9b19-67bf5937bd36
-- title:
--   Chart function on the branch `comp 1` reads as ̄ y(qᵖ)
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, and a subgroup $H\le(\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ under the reduction $(\mathbb{Z}/M)^\times\to(\mathbb{Z}/(M/p))^\times$; assume the Laurent series `jqModC ℚ` $=q^{-1}\cdot\sum$ (the rational $j$-series) lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level. Let $\mathfrak{P}$ be a term of `XHDRModelAtP p M H hpM hj`, the structure packaging the integral model over $R_p=\mathbb{Z}_{(p)}$ of the curves at levels $\Gamma_M$ and $\Gamma_N$ together with its properness, flatness, integrality, normality and smoothness data, the dictionary curve model over $\overline{\mathbb{Q}}$ with its pinning of chart functions against $q$-expansions, and the fibre data. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p\in A$ a nonunit, whose residue field $\kappa$ is of characteristic $p$ and algebraically closed, and let $\rho:R_p\to A$ be a ring map compatible with the structure map $R_p\to\overline{\mathbb{Q}}$. Let $b$ be an element of the $j$-finite chart algebra `chartAlgFin p (ΓN p M H hpM) hj` of the two-chart integral model at level $\Gamma_N$. Write $g$ for the composite `𝔓.efib A hA ρ hρ` followed by `𝔓.comp A hA ρ hρ 1` followed by the first projection of the pullback of `toBase p (ΓM M H) hj` along $\operatorname{Spec}$ of $\rho$ composed with the residue map of $A$, and $U=g^{-1}(\iota_{\mathrm{Fin}}(\top))$ for the preimage under $g$ of the open image of the $j$-finite chart at level $\Gamma_M$. The assertion is that $U$ is nonempty (as a scheme), and that for every Laurent series $y$ over $R_p$ whose coefficientwise image in $\mathbb{Q}((q))$ is the $q$-expansion of $b$, the following holds: take $\mathfrak{P}.\mathrm{iota0}\,b$ in the $j$-finite chart algebra at level $\Gamma_M$, view it as a section over $\iota_{\mathrm{Fin}}(\top)$ via the global sections isomorphism and the open immersion $\iota_{\mathrm{Fin}}$, pull it back along $g$ to a section over $U$, pass to its germ in the function field of `(𝔓.Mfib A hA ρ hρ).C` and transport it by the inverse of that model's function field identification; the resulting element of `qExpFunctionFieldC κ (ΓN p M H hpM)`, read in $\kappa((q))$, equals `qExpand κ p` applied to the coefficientwise reduction of $y$ to $\kappa$, i.e. $\bar y(q^p)$.
--
--   This records, at the level of functions on the integral fibre curve rather than of closed points, the classical fact of Deligne and Rapoport that on one of the two branches of the special fibre of the model at level $\Gamma_0(p)$-type structure the degeneracy map is the Frobenius substitution $q\mapsto q^{p}$; the companion statement on the other branch gives $\bar y(q)$. It is used by [`ModularCurve.XHDRModelAtP.restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb`](thm.html#ModularCurve.XHDRModelAtP.restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb), which turns the reading of chart functions into the identification of the restriction of the degeneracy map to that branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_one_iotaFin_iota0_eq_qExpand_coeffMap_of_mfib.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_one_iotaFin_iota0_eq_qExpand_coeffMap_of_mfib
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 1 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))),
    ∀ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
      (((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 1 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 1 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιFin p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (𝔓.iota0 b)))))
          : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        qExpand (IsLocalRing.ResidueField ↥A) p (coeffMap ((IsLocalRing.residue ↥A).comp ρ) y) := by sorry

-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
-- name    : ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/81231847-2567-512a-9ec0-6ab428e2ff25
-- title:
--   Pole-chart sections on the zeroth fibre component reduce q-expansions
-- statement:
--   Fix a prime $p$ and a non-zero natural number $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit mapping to $1$ under `ZMod.unitsMap` for $M/p \mid M$, and a witness `hj` that the Laurent series `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level. Let $\mathfrak{P}$ be a term of `XHDRModelAtP p M H hpM hj`, the structure packaging a proper flat integral model of the two-chart curve over $R\,p$ at level `ΓM M H` together with its auxiliary data. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p \in A$ a non-unit, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring homomorphism compatible with the structure map to $\overline{\mathbb{Q}}$. Let $b$ lie in `chartAlgInf p (ΓM M H) hj`, the `chartAlg` subalgebra of $\uparrow$`qExpFunctionFieldC ℚ (ΓM M H)` over $R\,p$ attached to the singleton $\{j^{-1}\}$, i.e. the coordinate ring of the chart at infinity. Consider the composite of `𝔓.efib A hA ρ hρ`, the component morphism `𝔓.comp A hA ρ hρ 0` and the first projection of the pullback of `toBase p (ΓM M H) hj` along `Spec` of the reduction $(\mathrm{residue}\ A) \circ \rho$, and let $U$ be the preimage under it of the image of the pole chart $\iota_{\inf}$. The assertion is that $U$ is non-empty and that, for every Laurent series $y$ over $R\,p$ whose coefficientwise image under $R\,p \to \mathbb{Q}$ is the $q$-expansion of $b$ in $\mathbb{Q}((q))$, transporting $b$ through the inverse of `Scheme.ΓSpecIso`, the inverse of the chart's `appIso`, the section map of the composite on $U$, the germ map to the function field of the curve underlying `𝔓.Mfib A hA ρ hρ` and the inverse of its `ffEquiv` gives an element of `qExpFunctionFieldC κ (ΓN p M H hpM)` whose Laurent series over $\kappa$ equals `coeffMap` of $(\mathrm{residue}\ A) \circ \rho$ applied to $y$.
--
--   This is the compatibility, on the chart at infinity, between reading a function of the level-`ΓM M H` integral model along the zeroth component of the fibre over a place above $p$ and reducing its $q$-expansion coefficientwise; it identifies the restriction of pole-chart functions to that component inside $\kappa((q))$. It is used by the corresponding statement for the finite chart, by the construction of Gauss witnesses for germs on the fibre, and by the computation of values at cusps of functions in the closure of the pole-chart algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve
open ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (b : ↥(chartAlgInf p (ΓM M H) hj)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))),
    ∀ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      (((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b))))
          : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap ((IsLocalRing.residue ↥A).comp ρ) y := by sorry

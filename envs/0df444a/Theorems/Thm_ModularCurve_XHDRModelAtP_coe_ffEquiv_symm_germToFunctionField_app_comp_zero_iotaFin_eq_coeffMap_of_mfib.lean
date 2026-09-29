-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
-- name    : ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/8a4d4b41-bfd1-56f6-a4fb-33c49c359180
-- title:
--   Finite-chart functions on the component Σ^∞ reduce to q-expansions
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \leq (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, and assume the Laurent series `jqModC ℚ` (namely $q^{-1}$ times the power series of the $j$-numerator) lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level. Let $\mathfrak{P}$ be a datum of type `XHDRModelAtP p M H hpM hj`: a proper, flat, locally finitely presented integral model $X$ over $\operatorname{Spec} R_p$ ($R_p =$ the localisation of $\mathbb{Q}$'s integers at $p$) with integrally closed sections on affine opens, a proper relatively one-dimensional smooth model at level $\Gamma_N(p,M,H)$, a curve model `Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` isomorphic over the base change to $X$, compatibly with the arithmetic Galois action and pinned so that finite-chart functions read off as their $q$-expansions, a smooth geometrically integral generic fibre, and further fields summarised here. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and $\rho : R_p \to A$ a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $b$ lie in `chartAlgFin p (ΓM M H) hj`, the $j$-finite chart subalgebra of `qExpFunctionFieldC ℚ (ΓM M H)` over $R_p$. The assertion is that the preimage of the $j$-finite chart open $\iota_{\mathrm{Fin}}(\top)$ under the composite $\mathfrak{P}.\mathrm{efib} \,\mathrel{;}\, \mathfrak{P}.\mathrm{comp}\,0 \,\mathrel{;}\, \mathrm{pr}_1$ into the base change of $X$ along $\operatorname{Spec}$ of $\kappa \circ \rho$ is nonempty, and that for every Laurent series $y$ over $R_p$ whose coefficientwise image under $R_p \to \mathbb{Q}$ is the $q$-expansion of $b$, the function-field element obtained by transporting $b$ through the chart isomorphisms, pulling it back along that composite, taking its germ at the generic point of the above preimage open, and identifying the function field of $\mathfrak{P}.\mathrm{Mfib}$ with `qExpFunctionFieldC κ (ΓN p M H hpM)`, equals, as an element of $\kappa((q))$, the coefficientwise reduction of $y$ under $\kappa \circ \rho$.
--
--   This is the dictionary statement that reading an integral $j$-finite-chart function on the component of the mod-$p$ fibre indexed by $0$ agrees with reducing its $q$-expansion coefficientwise; it is the $j$-finite counterpart of the corresponding statement for the $j$-infinite chart, which the proof cites together with the existence of integral lifts of $q$-expansions and the fraction-field property of $R_p$. It is used in the identification of Gauss witnesses, in the regularity criterion for places attached to closed points, and in the computation of orders of vanishing at places outside the $q$-expansion singular set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve
open ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))),
    ∀ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      (((𝔓.Mfib A hA ρ hρ).ffEquiv.symm
          ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
            ((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.efib A hA ρ hρ ≫ 𝔓.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
                (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιFin p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))))
          : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap ((IsLocalRing.residue ↥A).comp ρ) y := by sorry

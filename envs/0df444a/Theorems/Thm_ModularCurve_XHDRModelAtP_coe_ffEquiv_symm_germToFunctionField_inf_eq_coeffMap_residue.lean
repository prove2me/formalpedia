-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue
-- name    : ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/bfe78617-1ae8-506b-acdc-b7725e3ff176
-- title:
--   Pole-chart functions read on the special fibre reduce coefficientwise
-- statement:
--   Fix a prime $p$ and $M$ with $M \neq 0$, a subgroup $H \leq (\mathbb{Z}/M)^{\times}$, hypotheses $p \mid M$ and $p^2 \nmid M$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` $= q^{-1}\cdot\mathrm{jNum}$ lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the full-level integral form ratios. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, the bundle of models and properties for the curve at level $H$ over `R p`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho \colon$ `R p` $\to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Assume the open subscheme $U$, the preimage under $\mathfrak{X}$`.efib` followed by `pullback.fst` of the image of the $j^{-1}$-chart immersion `ιInf` at level `ΓN p M H hpM`, is non-empty. Then for every $b$ in the pole chart algebra `chartAlgInf p (ΓN p M H hpM) hj` and every $y \in A((q))$ whose coefficientwise image in $\overline{\mathbb{Q}}((q))$ is the $q$-expansion of $b$: transporting $b$ to a section over $U$, taking its germ in the function field of $\mathfrak{X}$`.Mfib`, and identifying that field with `qExpFunctionFieldC (ResidueField A) (ΓN p M H hpM)` via `ffEquiv.symm`, gives the Laurent series obtained from $y$ by applying the residue map to each coefficient.
--
--   This is the $j^{-1}$-chart analogue, on the special fibre at a level where $p$ exactly divides $M$, of the normalisation clause imposed on the $j$-chart inside the model bundle: functions of either chart are read in the reduced $q$-expansion field as the coefficientwise reductions of their integral $q$-expansions. It is used in identifying the place attached to a point of the special fibre, and in the criterion for such a place to be cuspidal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffMap_residue
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))) :
    (((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
        ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField
          ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
            ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          (((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
              ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
            (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b))))
        : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) y := by sorry

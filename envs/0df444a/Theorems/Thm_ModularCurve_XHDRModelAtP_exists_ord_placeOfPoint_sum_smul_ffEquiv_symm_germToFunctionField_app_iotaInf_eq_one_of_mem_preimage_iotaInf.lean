-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf
-- name    : ModularCurve.XHDRModelAtP.exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/e1cac78b-f960-5db7-9493-3b2a21dc86be
-- title:
--   Uniformiser at a pole-chart point of the special fibre
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ (and $M/p$ nonzero), a subgroup $H \le (\mathbb{Z}/M)^\times$, and a hypothesis `hj` saying that the Laurent series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by the full-level integral form ratios. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which bundles the properness, flatness, integrality, normality and finite-presentation data for the two-chart models `toBase p (ΓM M H) hj` and `toBase p (ΓN p M H hpM) hj`, a curve model of the geometric function field together with its comparison isomorphism, Galois equivariance and chart-reading identities. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, i.e. the image of $p$ lies in the nonunits of $A$, whose residue field $\kappa =$ `IsLocalRing.ResidueField A` is of characteristic $p$ and algebraically closed, and let $\rho : R p \to A$ be a ring homomorphism whose composition with the inclusion of $A$ is the structure map $R p \to \overline{\mathbb{Q}}$. Write $\mathcal{M} = \mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$ for the associated curve model over $\kappa$, with function field identified by `ffEquiv` with `qExpFunctionFieldC κ (ΓN p M H hpM)`, and $e = \mathfrak{X}.\mathrm{efib}$ for its comparison morphism to the pullback of `toBase p (ΓN p M H hpM) hj` along $\operatorname{Spec}$ of the reduction $R p \to \kappa$ of $\rho$. Let $P$ be a closed point of $\mathcal{M}.C$ whose image under $e$ lies in the preimage under `pullback.fst` of the open image of $\top$ under the pole-chart immersion `ιInf p (ΓN p M H hpM) hj`. Then that preimage open subscheme of $\mathcal{M}.C$ along $e$ followed by `pullback.fst` is nonempty, and there are $n \in \mathbb{N}$, elements $c_1,\dots,c_n$ of the pole-chart algebra `chartAlgInf p (ΓN p M H hpM) hj` and scalars $a_1,\dots,a_n \in \kappa$ such that the function $\sum_i a_i \cdot r(c_i)$ has $\operatorname{ord} = 1$ at the place $\mathcal{M}.\mathrm{placeOfPoint}\,P$, where $\operatorname{ord}$ is minus the logarithm of the adic valuation and $r(c)$ denotes the element of `qExpFunctionFieldC κ (ΓN p M H hpM)` obtained from $c$ by transporting through the global-sections isomorphism of $\operatorname{Spec}$ of the pole-chart algebra and the section isomorphism of `ιInf`, pulling back along $e$ followed by `pullback.fst`, taking the germ into the function field of $\mathcal{M}.C$, and applying `ffEquiv.symm`. In other words, some $\kappa$-linear combination of readings of pole-chart functions is a uniformiser at $P$.
--
--   This produces a uniformiser, of a prescribed shape, at a closed point of the good-reduction fibre of the Deligne–Rapoport type model lying over the chart around the cusps (the $j^{-1}$ chart). It is used in the construction of prolongation data for regular sections, via [`ModularCurve.XHDRModelAtP.exists_lift_regular_section_comp_zero_ord_placeOfPoint_eq_one_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.exists_lift_regular_section_comp_zero_ord_placeOfPoint_eq_one_prolongationDatum), and rests on the description of the stalks over the pole chart as localisations of `chartAlgInf ⊗ O`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ).base P.1 ∈ (pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))))
      (n : ℕ) (c : Fin n → ↥(chartAlgInf p (ΓN p M H hpM) hj)) (a : Fin n → IsLocalRing.ResidueField ↥A),
      ((𝔛.Mfib A hA ρ hρ).placeOfPoint P).ord
        (∑ i, algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) (a i) *
          ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
            ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField
              ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                  (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
              (((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                  (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv (c i))))))) = 1 := by sorry

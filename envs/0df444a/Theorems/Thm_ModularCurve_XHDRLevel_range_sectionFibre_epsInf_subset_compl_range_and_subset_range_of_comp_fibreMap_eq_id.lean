-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id
-- name    : ModularCurve.XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/4973f24b-a31e-5ac7-9953-864768aee897
-- title:
--   Cusp ∞ reduces onto comp₀, off comp₁
-- statement:
--   Fix a prime $p$, a nonzero $M$ and a subgroup $H\le(\mathbb Z/M)^\times$ with $p\mid M$, $p^2\nmid M$ and such that every unit of $\mathbb Z/M$ whose image under `ZMod.unitsMap` in $(\mathbb Z/(M/p))^\times$ is $1$ lies in $H$, and assume the Laurent series `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by ratios of integral $q$-expansions of modular forms of full level. The data are: a section $\varepsilon_\infty$ of `toBase p (ΓM M H) hj` over the identity of $\operatorname{Spec}(R p)$; an $R p$-algebra map $\rho_\infty$ from the chart algebra `chartAlgInf` at level `ΓM M H` (elements of the function field integral over $R p[j^{-1}]$) to $R p$ sending $b$ to the $q$-expansion coefficient of $b$ in degree $0$, such that $\varepsilon_\infty$ factors as $\operatorname{Spec}\rho_\infty$ followed by the chart inclusion `ιInf`; a morphism $\pi$ from `toBase p (ΓM M H) hj` to `toBase p (ΓN p M H hpM) hj` over $\operatorname{Spec}(R p)$, pinned on the finite chart by an $R p$-algebra map $\iota_0:$ `chartAlgFin` at level `ΓN p M H hpM` $\to$ `chartAlgFin` at level `ΓM M H` preserving $q$-expansions, and on the infinite chart by the analogous $\iota_\infty$; an $R p$-algebra automorphism $\theta$ of `chartAlgFin` at level `ΓM M H` with $\theta(\iota_0 b)$ having $q$-expansion `qExpand ℚ p` of that of $b$, i.e. $q\mapsto q^p$; a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, algebraically closed residue field $\kappa$ of characteristic $p$, and a ring map $\rho:R p\to A$ compatible with the structure map $R p\to\overline{\mathbb Q}$. Finally let $\mathrm{comp}_0,\mathrm{comp}_1$ be closed immersions from the fibre at level `ΓN p M H hpM` to the fibre at level `ΓM M H` over $\kappa$ (fibres being the pullbacks of the structure maps along $\operatorname{Spec}$ of the residue map of $A$ composed with $\rho$), both commuting with the projections to $\operatorname{Spec}\kappa$, with $\mathrm{comp}_0$ a section of `fibreMap π` and with every point of the fibre at level `ΓM M H` lying in the image of $\mathrm{comp}_0$ or of $\mathrm{comp}_1$. The conclusion is that the image of the underlying map of `sectionFibre εinf` for the residue map of $A$ composed with $\rho$, the $\kappa$-point of the fibre induced by $\varepsilon_\infty$, is contained in the complement of the image of $\mathrm{comp}_1$ and contained in the image of $\mathrm{comp}_0$.
--
--   This is the statement that the cusp $\infty$ of the $\Gamma_H(M)$ model over $R p$ specialises, in the fibre at $p$ when $p\parallel M$, to a point of the component on which the forgetful map to level $\Gamma_{H'}(M/p)$ is inverted by $\mathrm{comp}_0$, and to no point of the other component; the two-component decomposition is the Deligne–Rapoport picture of the fibre at $p$. It is used by [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart) in assembling the model at $p$ together with its Atkin–Lehner data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra ModularCurve
open ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.range_sectionFibre_epsInf_subset_compl_range_and_subset_range_of_comp_fibreMap_eq_id
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    (rhoInf : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] R p)
    (rhoInf_spec : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ((rhoInf b : R p) : ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ).coeff 0)
    (εinf_chart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ ιInf p (ΓM M H) hj)

    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)

    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))

    (iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (pi_chartInf : ιInf p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (comp0 : fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := (ΓM M H)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hcomp_over : comp0 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp_ci : IsClosedImmersion comp0]
    (hcomp_pi : comp0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _)

    (comp1 : fibre (Γ := (ΓN p M H hpM)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := (ΓM M H)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hcomp1_over : comp1 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp1_ci : IsClosedImmersion comp1]
    (hjoint : ∀ y : ↥(fibre (Γ := (ΓM M H)) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), y ∈ Set.range comp0.base ∨ y ∈ Set.range comp1.base) :
    Set.range (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ (Set.range comp1.base)ᶜ ∧
      Set.range (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range comp0.base := by sorry

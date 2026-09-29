-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one
-- name    : ModularCurve.XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/aec2e72f-5e07-51c3-9062-41032c6363bd
-- title:
--   Section avoiding the second component lies in the smooth open
-- statement:
--   Fix a prime $p$, an integer $M\ge 1$ with $p\mid M$, a subgroup $H\le(\mathbb{Z}/M)^{\times}$, and a witness `hj` that the Laurent series `jqModC ℚ` lies in the field $\mathbb{Q}(\,\text{integral form ratios at level }\mathrm{SL}_2(\mathbb{Z})\,)$, so that the two-chart integral models $X$ at levels $\Gamma_H(M)$ and $\Gamma_{H}(M,p)$ over $\operatorname{Spec}$ of the base ring `R p` are available. Assume the structure morphism `toBase p (ΓM M H) hj` is flat and locally of finite presentation and that `toBase p (ΓN p M H hpM) hj` is smooth of relative dimension $1$. Let $U$ be an open subscheme of `X p (ΓM M H) hj` that contains every open $V$ whose inclusion followed by `toBase p (ΓM M H) hj` is smooth. Assume that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, whose residue field is algebraically closed of characteristic $p$, and every ring map $\rho\colon$ `R p` $\to A$ compatible with the structure map to $\overline{\mathbb{Q}}$, writing $\kappa$ for the residue field and taking fibres (pullbacks along $\operatorname{Spec}$ of the composite of $\rho$ with the residue map): the level-$\Gamma_H(M)$ fibre is reduced, and there are given two morphisms $\mathrm{comp}_0,\mathrm{comp}_1$ from the level-$\Gamma_H(M,p)$ fibre to it, each commuting with the second projections to $\operatorname{Spec}\kappa$, each a closed immersion, and jointly surjective on points. Let $\varepsilon$ be a morphism $\operatorname{Spec}$ `R p` $\to$ `X p (ΓM M H) hj` composing with `toBase` to the identity, and assume that for all such $A,\rho$ the image of the induced $\kappa$-section `sectionFibre ε` of the fibre is disjoint from the image of $\mathrm{comp}_1$. Then the set-theoretic image of $\varepsilon$ is contained in $U$.
--
--   This is the statement that the cusp section of a Deligne–Rapoport-type integral model of $X_H(M)$ at a prime $p$ exactly dividing $M$ lands in the smooth locus, proved for an arbitrary section over the base ring whose reduction avoids the second of the two components of the special fibre, with no local computation at the cusp. It feeds the construction of a generic chart for the model with its Atkin–Lehner data, [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicCurve NeronModelInfra ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRLevel.range_section_subset_of_forall_range_sectionFibre_subset_compl_range_comp_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    [Flat (toBase p (ΓM M H) hj)] [LocallyOfFinitePresentation (toBase p (ΓM M H) hj)]
    [SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj)]
    (U : (X p (ΓM M H) hj).Opens)
    (hUmax : ∀ V : (X p (ΓM M H) hj).Opens, Smooth (V.ι ≫ toBase p (ΓM M H) hj) → V ≤ U)
    (fibre_reduced : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
        fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (comp_over : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
      comp A hA ρ hρ i ≫ pullback.snd _ _ = pullback.snd _ _)
    (comp_isClosedImmersion : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
      IsClosedImmersion (comp A hA ρ hρ i))
    (comp_jointly_surjective : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
      (y : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      y ∈ Set.range (comp A hA ρ hρ 0).base ∨ y ∈ Set.range (comp A hA ρ hρ 1).base)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    (ε_off_comp1 : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
      Set.range (sectionFibre ε ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ (Set.range (comp A hA ρ hρ 1).base)ᶜ) :
    Set.range ε.1.base ⊆ (U : Set (X p (ΓM M H) hj)) := by sorry

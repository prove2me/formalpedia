-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia
-- name    : ModularCurve.XHDRModelAtP.exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/900b2ba0-64f6-5ad6-9942-d637c06740f9
-- title:
--   Pole-chart morphism to the special fibre intertwining a diamond
-- statement:
--   Fix a prime $p$, an integer $M \neq 0$ with $p \mid M$, a subgroup $H \leq (\mathbb{Z}/M)^{\times}$, and a proof `hj` that the Laurent series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms of full level; let $\mathfrak{P}$ be a bundle `XHDRModelAtP p M H hpM hj` of data and properties for the two-chart integral model `X p (ΓM M H) hj` over `Spec (R p)`, among them isomorphisms `𝔓.dia d` of that model lying over its structure morphism `toBase`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, whose residue field $\kappa$ is algebraically closed of characteristic $p$, let $\rho : R p \to A$ be a ring homomorphism with $A \hookrightarrow \overline{\mathbb{Q}}$ after $\rho$ equal to the structure map $R p \to \overline{\mathbb{Q}}$, and let $\kappa$ carry an `R p`-algebra structure whose structure map is $\rho$ followed by the residue map. Let $d \in (\mathbb{Z}/M)^{\times}$ and let $\sigma$ be an `R p`-algebra automorphism of the pole-chart algebra $O =$ `chartAlgInf p (ΓM M H) hj`, the subalgebra of elements of the function field `qExpFunctionFieldC ℚ (ΓM M H)` integral over `R p` adjoin $j^{-1}$, and assume that the open immersion `ιInf` followed by `(𝔓.dia d).hom` equals `Spec σ` followed by `ιInf`. The conclusion asserts the existence of a morphism $c' : \operatorname{Spec}(\kappa \otimes_{R p} O) \to$ `fibre ((IsLocalRing.residue A).comp ρ)`, the pullback of `toBase` along $\operatorname{Spec}$ of $\rho$ followed by the residue map, such that: $c'$ followed by the first projection equals $\operatorname{Spec}$ of the inclusion $O \to \kappa \otimes_{R p} O$ followed by `ιInf`; $c'$ followed by the second projection equals $\operatorname{Spec}$ of the inclusion $\kappa \to \kappa \otimes_{R p} O$; and $\operatorname{Spec}(\mathrm{id}_\kappa \otimes \sigma)$ followed by $c'$ equals $c'$ followed by `fibreMap` of `𝔓.dia d`, viewed via `overOfIso` as a morphism over `toBase`, base changed to $\kappa$.
--
--   This realises the pole chart of the special fibre of the model of $X_H(M)$ at $p$ as a $\kappa$-point-level morphism into the fibre, together with the compatibility of the diamond automorphism $\langle d \rangle$ with its description $\sigma$ on the chart ring. It is used to compare ideals of the chart ring with subschemes of the special fibre, and in the analysis of the action of diamond automorphisms on $q$-expansions at a given level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRModelAtP.exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) (IsLocalRing.ResidueField ↥A)]
    (halg : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ)
    (d : (ZMod M)ˣ)
    (σ : ↥(chartAlgInf p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (hdia : ιInf p (ΓM M H) hj ≫ (𝔓.dia d).hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιInf p (ΓM M H) hj) :
    ∃ c' : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
        fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
      c' ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫
          ιInf p (ΓM M H) hj ∧
      c' ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓM M H) hj)))) ∧
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (R p) (IsLocalRing.ResidueField ↥A)) (σ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] _)).toRingHom) ≫ c' =
        c' ≫ fibreMap (overOfIso (𝔓.dia d) (𝔓.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ) := by sorry
